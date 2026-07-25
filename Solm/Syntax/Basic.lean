import EVM.Types
import ABI.Types

namespace Solm

open ABI

abbrev Ident := String

/- Basically all values that can be a key for a mapping.
  In other words all types that can fit in a word. -/
inductive KeyValue where
  | int : Int -> KeyValue
  | bool : Bool -> KeyValue
  | address : EVM.Address -> KeyValue
  | fixedBytes : Fin 32 -> List UInt8 -> KeyValue
  deriving Repr, Inhabited

/- Storage deref step. -/
inductive EvaledStorageRefStep where
  | field : Ident -> EvaledStorageRefStep
  | tupleElem : Nat -> EvaledStorageRefStep
  | mindex : KeyValue -> EvaledStorageRefStep
  | aindex : KeyValue -> EvaledStorageRefStep
  /- Accessor for the slot that holds the length of an array. -/
  | length : EvaledStorageRefStep
  deriving Repr, Inhabited

/- The evaluated path to a storage reference. -/
structure EvaledStorageRef where
  base : Ident
  steps : List EvaledStorageRefStep := []
  deriving Repr, Inhabited

/- The types that can be in storage -/
inductive StorageType where
  | elem : ElemType -> StorageType
  | mapping : ElemType -> StorageType -> StorageType  -- Check more on Keytype here
  | contract : Ident -> StorageType
  -- Keeping the fields inside the struct so that recursion over StorageType is well-founded
  -- So right now this refers to the AST, not the surface syntax
  | struct : Ident -> List (Ident × StorageType) -> StorageType
  | tuple : List StorageType -> StorageType
  | array : StorageType -> Nat -> StorageType
  | dynamicArray : StorageType -> StorageType
  -- Conditionally compact layout used by solidity for bytes and strings
  | bytes : StorageType
  | string : StorageType
  deriving Repr, Inhabited

/- Ethereum environment variables -/
inductive EnvVar where
  | caller
  | origin
  | callvalue
  | this
  | timestamp
  | chainid
  | selfbalance
  | gasprice
  | number
  | coinbase
  | gaslimit
  | prevrandao
  | basefee
  | msgSig
  | msgData
  deriving Repr, Inhabited

inductive UnaryOp where
  | not
  | neg
  | bitNot
  deriving Repr, Inhabited

inductive BinaryOp where
  | add
  | sub
  | mul
  | div
  | mod
  | eq
  | ne
  | lt
  | le
  | gt
  | ge
  | and
  | or
  | bitAnd
  | bitOr
  | bitXor
  | shl
  | shr
  | exp
  deriving Repr, Inhabited

/-- Whether a variable path is rooted in a memory **local** or **storage**.
    Resolved statically, similar to solc. -/
inductive VarOrigin where
  | localVar
  | storage
  deriving Repr, Inhabited

mutual

/-
 - Expressions.
 - In Solm, expressions are pure and side-effect free (similar to Clight).
 - All stateful operations are statements.
 -/
inductive Expr where
  | intLit : Int -> Expr
  | boolLit : Bool -> Expr
  | bytesLit : ByteArray -> Expr
  /- `new bytes(len)`: a fresh zero-filled byte string of dynamic length `len` -/
  | newBytes : Expr -> Expr
  /- `new T[](len)`: a fresh memory array with `len` default-initialized elements of type `T` -/
  | newArray : StorageType -> Expr -> Expr
  /- struct literal `S({field₁: e₁, …})`: builds a `Value.struct` from the named field expressions
     (e.g. `Proposal({name: x, voteCount: 0})`). -/
  | structLit : Ident -> List (Ident × Expr) -> Expr
  /- array literal `[e₁, …]`: builds a `Value.array` from the element expressions. -/
  | arrayLit : List Expr -> Expr
  /- tuple literal: builds a `Value.tuple` from the element expressions.  Used to assemble a
     multi-value (tuple) return (e.g. a struct getter returning `(a, b)`); its value representation
     is `Value.tuple`, distinct from `Value.array`. -/
  | tupleLit : List Expr -> Expr
  /- static tuple projection `t.i`: the `i`-th component. -/
  | tupleGet : Expr -> Nat -> Expr
  /- `b[start:end]`: byte slice of dynamic bytes `b` over `[start, end)` -/
  | bytesSlice : Expr /- base -/ -> Expr /- start -/ -> Expr /- end -/ -> Expr
  | var : Ident -> Expr
  | env : EnvVar -> Expr
  /- for struct fields -/
  | field : Expr -> Ident -> Expr
  /- Storage reference -/
  | storage : StorageRef -> Expr
  /- Predicate asserting that an integer expression is within the range of the specified type. -/
  | inRange : IntType -> Expr -> Expr
  | cast : Expr -> StorageType -> Expr /- TODO do we really need casting?-/
  | addrOf : Expr -> Expr
  | unary : UnaryOp -> Expr -> Expr
  | binary : BinaryOp -> Expr -> Expr -> Expr
  | index : Expr -> Expr -> Expr
  | ite : Expr -> Expr -> Expr -> Expr
  /- `arr.length`. The origin is explicit, matching assignment: storage paths read the declared
     storage array length; local paths read the in-memory value and return its array/byte count. -/
  | arrayLength : VarOrigin -> StorageRef -> Expr
  /- `keccak256(b)`: the Keccak-256 hash of the dynamic bytes `b`, as a `bytes32` value.  The hash
     primitive is the same `ffi.KEC` the EVM's `KECCAK256` opcode uses. -/
  | keccak256 : Expr -> Expr
  /- `abi.encodePacked(e₁, …)`: the non-padded ("packed") ABI encoding of the listed values, as a
     dynamic `bytes`.  Each operand carries its (statically known) `ABIType`, which fixes its packed
     width (`uintN`→N/8 bytes, `bool`→1, `address`→20, `bytesN`→N, with no length prefixes). -/
  | abiEncodePacked : List (ABIType × Expr) -> Expr
  /- ABI calldata for a configured external call, including the 4-byte selector.  The contract's
     `Config.externalABI.encode?` determines the selector/types for `name`; this models
     `abi.encodeWithSelector(...)` without baking contract-specific selectors into Solm. -/
  | abiEncodeCall : Ident -> List Expr -> Expr
  /- `abi.decode(bytes, (T))`: decode a single ABI return value from dynamic bytes.  Decode failure is
     a model-level revert, matching Solidity's runtime `abi.decode` behavior. -/
  | abiDecode : ABIType -> Expr -> Expr
  /- `addr.code.length` (EXTCODESIZE): the size in bytes of the code deployed at address `addr`.
     Matches `Ethereum.State.extCodeSize` — a non-existent account or an EOA (no code) has size 0.
     Used by ERC721 `safeTransferFrom`'s `to.code.length == 0` contract-detection guard. -/
  | extCodeSize : Expr -> Expr
  /- `addr` code prefix (EXTCODECOPY): the first `len` bytes of the code at `addr`, as `bytes`,
     zero-padded past the code end (all zero for a non-existent account or an EOA). -/
  | extCodePrefix : Expr /- addr -/ -> Expr /- len -/ -> Expr
  /- `blockhash(n)` (BLOCKHASH), `addr.balance` (BALANCE), `addr.codehash` (EXTCODEHASH). -/
  | blockhash : Expr -> Expr
  | balanceOf : Expr -> Expr
  | extCodeHash : Expr -> Expr
  /- Fixed-size `bytesN` literal: the ABI type index (`n : Fin 32` ⇒ width `n+1`) and the bytes in
     Solidity order.  Models compile-time `bytesN` constants — hex `bytesN` literals, a function's
     `.selector` (`bytes4`), and `type(I).interfaceId` (`bytes4`) — all of which solc bakes as PUSH
     immediates.  Evaluates to `Value.fixedBytes n bs`; `==`/comparisons already act on `fixedBytes`. -/
  | fixedBytesLit : Fin 32 -> List UInt8 -> Expr

inductive StorageRefStep where
  | field : Ident -> StorageRefStep
  | mindex : Expr -> StorageRefStep
  | aindex : Expr -> StorageRefStep

/- A reference to storage. The base variable is either a storage variable or a local variable alias. -/
structure StorageRef where
  base : Ident
  steps : List StorageRefStep := []

end

namespace StorageRef

def var (name : Ident) : StorageRef :=
  { base := name }

end StorageRef

instance : Repr ByteArray where
  reprPrec b _ := repr b.data

deriving instance Repr for Expr
deriving instance Inhabited for Expr
deriving instance Repr for StorageRefStep
deriving instance Inhabited for StorageRefStep
deriving instance Repr for StorageRef
deriving instance Inhabited for StorageRef

inductive AssignRhs where
  | expr : Expr -> AssignRhs
  -- Do we want non-determinism?
  -- | havoc
  deriving Repr, Inhabited

inductive Stmt where
  /- local variable declaration (values are in-memory copies)-/
  | letDecl : Ident -> Option ABIType -> Expr -> Stmt
  /- local storage alias (values are evaluated storage references) -/
  | letStorage : Ident -> StorageRef -> Stmt
  /- `uint256 x = gasleft()`: bind `x` to a nondeterministic gas value (Solm tracks no gas). -/
  | letGas : Ident -> Stmt
  /- assignment to a local (`.local`) or storage (`.storage`) variable path -/
  | assign : VarOrigin -> StorageRef -> Expr -> Stmt
  | require : Expr -> Stmt
  | while : Expr -> List Stmt -> Stmt
  /- `for (init; cond; post) { body }`, modelled as Yul's `for {init} cond {post} {body}`:
     `init` runs once, then each iteration checks `cond`, runs `body`, then `post`.  A `continue`
     in `body` skips to `post` (re-checking `cond` after); a `break` exits without running `post`. -/
  | for : List Stmt /- init -/ -> Expr /- cond -/ -> List Stmt /- post -/ -> List Stmt /- body -/ -> Stmt
  /- conditional: `if cond { thenBranch } else { elseBranch }`; a no-`else` `if` is `elseBranch = []` -/
  | ite : Expr -> List Stmt -> List Stmt -> Stmt
  /- constructor call: `salt = none` ⇒ CREATE, `some e` (bytes32) ⇒ CREATE2. -/
  | new : Ident -> Expr /- ETH to send -/ -> List Expr -> Ident /- return value binder -/ ->
      (salt : Option Expr := none) -> Stmt
  /- internal and external call results are explicitly let-bound -/
  | internalCall : Ident -> List Expr -> Ident /- return value binder -/ -> Stmt
  | externalCall : Expr -> Ident -> Expr /- ETH to send -/ -> List Expr ->
      Ident /- return value binder -/ -> (perm : Bool := true) -> Stmt
  /- low-level raw call, binds a success `bool` to `okVar` and raw returndata to `dataVar`.
     `perm = true` models `.call`; `perm = false` models raw `.staticcall`. -/
  | lowLevelCall : Expr /- target -/ -> Expr /- ETH to send -/ ->
      Expr /- calldata bytes -/ -> Ident /- success binder -/ ->
      Ident /- raw returndata binder -/ -> (perm : Bool := true) -> Stmt
  /- low-level raw delegatecall, binds a success `bool` to `okVar` and raw returndata to
     `dataVar`.  There is no ETH argument: EVM `DELEGATECALL` preserves `msg.value` and transfers
     no value. -/
  | delegateCall : Expr /- target -/ -> Expr /- calldata bytes -/ ->
      Ident /- success binder -/ -> Ident /- raw returndata binder -/ -> Stmt
  /- `try recv.name{value}(args) returns (retVar) { onSuccess } catch { onFail }`.  All callee
     reverts hand control to `onFail` with the raw revert bytes bound to `errVar`; the spec filters by
     selector prefix (e.g. `Error(string)`) and re-reverts uncaught cases via `require false`.
     `retVar` is bound only within `onSuccess`. -/
  | checkedCall : Expr /- receiver -/ -> Ident /- name -/ -> Expr /- ETH -/ ->
      List Expr /- args -/ -> Ident /- decoded return, scoped to onSuccess -/ ->
      List Stmt /- onSuccess -/ -> Ident /- raw revert bytes, scoped to onFail -/ ->
      List Stmt /- onFail -/ -> (perm : Bool := true) -> Stmt
  /- `return (e₁, …, eₙ)`: return the listed values.  `[]` models `return;` / a void return. -/
  | return : List Expr -> Stmt
  | break : Stmt
  | continue : Stmt
  /- `arr.push(v?)`: grow a dynamic storage array by one.  `some v` appends scalar `v`; `none` is a
     grow-only push (the new slots are zero). -/
  | push : StorageRef -> Option Expr -> Stmt
  /- `arr.pop()`: remove the last element of a dynamic storage array (reverts if empty),
     clearing the slot and shrinking its length by one -/
  | pop : StorageRef -> Stmt
  /- `delete x`: reset the storage at `x` to its zero value (recursively, per its type) -/
  | delete : StorageRef -> Stmt
  deriving Repr, Inhabited


/-- Body of a function, constructor, or transition is a sequence of statements. -/
abbrev Body := List Stmt

structure Param where
  name : Ident
  ty : ABI.ABIType
  deriving Repr, Inhabited

structure StorageDecl where
  name : Ident
  ty : StorageType
  deriving Repr, Inhabited

structure ConstructorDecl where
  params : List Param
  body : List Stmt
  deriving Repr, Inhabited

-- Currently this covers storage structs
-- The ABI technically has no structs,
-- Solidity implements call-parameter structs through ABI tuples
structure StructDecl where
  name : Ident
  fields : List StorageDecl
  deriving Repr, Inhabited

/- For now, internal function interface only accept ABI types.
 - In the future, we may extend this with non-ABI types as well (e.g., mappings). -/
structure FunctionDecl where
  name : Ident
  params : List Param
  /-- ABI return types (potentially, multi-element; `[]` = void) -/
  returnType : List ABIType := []
  body : List Stmt
  deriving Repr, Inhabited

structure TransitionDecl where
  name : Ident
  params : List Param
  /-- ABI return types (potentially, multi-element; `[]` = void) -/
  returnType : List ABIType := []
  body : List Stmt
  deriving Repr, Inhabited

/- A top-level contract declaration. -/
structure ContractDecl where
  name : Ident
  storage : List StorageDecl
  ctor : ConstructorDecl
  structs : List StructDecl := [] -- Maybe these should not be per-contract. Zoe: if we are inlining them anyway, do we still need this?
  functions : List FunctionDecl := []
  transitions : List TransitionDecl := []
  receive : Option TransitionDecl := none
  fallback : Option TransitionDecl := none
  deriving Repr, Inhabited

abbrev Program := List ContractDecl

end Solm
