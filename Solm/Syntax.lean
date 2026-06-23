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
  deriving DecidableEq, Repr, Inhabited

inductive EvaledStorageRefStep where
  | field : Ident -> EvaledStorageRefStep
  | tupleElem : Nat -> EvaledStorageRefStep
  | mindex : KeyValue -> EvaledStorageRefStep
  | aindex : KeyValue -> EvaledStorageRefStep
  /- Marker for "the length of the array reached so far". A distinct ref the layout
     resolves to wherever it stores that array's length — the semantics commits to no
     particular slot convention (solc puts it at the array's base slot; another layout
     may put it elsewhere). Only the array's length query produces this step. -/
  | length : EvaledStorageRefStep
  deriving DecidableEq, Repr, Inhabited

structure EvaledStorageRef where
  base : Ident
  steps : List EvaledStorageRefStep := []
  deriving DecidableEq, Repr, Inhabited

/- Storage slots may either hold Elementary ABI values or nested mappings. -/
-- Note: name changed from StorageRefType, because in Solidity terminology
-- a slot is a storage word, not a location for an item in storage
-- of which there may be multiple in a given word
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

mutual
  private def StorageType.decEq : (a b : StorageType) -> Decidable (a = b)
    | .elem p, .elem q =>
        match (inferInstance : Decidable (p = q)) with
        | isTrue h => isTrue (by subst q; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .mapping k t, .mapping l u =>
        match (inferInstance : Decidable (k = l)), StorageType.decEq t u with
        | isTrue hk, isTrue ht => isTrue (by subst l; subst u; rfl)
        | isFalse hk, _ => isFalse (by intro h'; cases h'; exact hk rfl)
        | _, isFalse ht => isFalse (by intro h'; cases h'; exact ht rfl)
    | .contract x, .contract y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .struct x fx, .struct y fy =>
        match (inferInstance : Decidable (x = y)), StorageType.decEqNamedList fx fy with
        | isTrue h, isTrue hf => isTrue (by subst y; cases hf; rfl)
        | _, isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
        | isFalse h, _ => isFalse (by intro h'; cases h'; exact h rfl)
    | .tuple xs, .tuple ys =>
        match StorageType.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .array t n, .array u m =>
        match StorageType.decEq t u, (inferInstance : Decidable (n = m)) with
        | isTrue ht, isTrue hn => isTrue (by subst u; subst m; rfl)
        | isFalse ht, _ => isFalse (by intro h'; cases h'; exact ht rfl)
        | _, isFalse hn => isFalse (by intro h'; cases h'; exact hn rfl)
    | .dynamicArray t, .dynamicArray u =>
        match StorageType.decEq t u with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .bytes, .bytes => isTrue rfl
    | .string, .string => isTrue rfl
    | .elem _, .mapping _ _ => isFalse (by intro h; cases h)
    | .elem _, .contract _ => isFalse (by intro h; cases h)
    | .elem _, .struct _ _ => isFalse (by intro h; cases h)
    | .elem _, .tuple _ => isFalse (by intro h; cases h)
    | .elem _, .array _ _ => isFalse (by intro h; cases h)
    | .elem _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .elem _, .bytes => isFalse (by intro h; cases h)
    | .elem _, .string => isFalse (by intro h; cases h)
    | .mapping _ _, .elem _ => isFalse (by intro h; cases h)
    | .mapping _ _, .contract _ => isFalse (by intro h; cases h)
    | .mapping _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .mapping _ _, .tuple _ => isFalse (by intro h; cases h)
    | .mapping _ _, .array _ _ => isFalse (by intro h; cases h)
    | .mapping _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .mapping _ _, .bytes => isFalse (by intro h; cases h)
    | .mapping _ _, .string => isFalse (by intro h; cases h)
    | .contract _, .elem _ => isFalse (by intro h; cases h)
    | .contract _, .mapping _ _ => isFalse (by intro h; cases h)
    | .contract _, .struct _ _ => isFalse (by intro h; cases h)
    | .contract _, .tuple _ => isFalse (by intro h; cases h)
    | .contract _, .array _ _ => isFalse (by intro h; cases h)
    | .contract _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .contract _, .bytes => isFalse (by intro h; cases h)
    | .contract _, .string => isFalse (by intro h; cases h)
    | .struct _ _, .elem _ => isFalse (by intro h; cases h)
    | .struct _ _, .mapping _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .contract _ => isFalse (by intro h; cases h)
    | .struct _ _, .tuple _ => isFalse (by intro h; cases h)
    | .struct _ _, .array _ _ => isFalse (by intro h; cases h)
    | .struct _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .struct _ _, .bytes => isFalse (by intro h; cases h)
    | .struct _ _, .string => isFalse (by intro h; cases h)
    | .tuple _, .elem _ => isFalse (by intro h; cases h)
    | .tuple _, .mapping _ _ => isFalse (by intro h; cases h)
    | .tuple _, .contract _ => isFalse (by intro h; cases h)
    | .tuple _, .struct _ _ => isFalse (by intro h; cases h)
    | .tuple _, .array _ _ => isFalse (by intro h; cases h)
    | .tuple _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .tuple _, .bytes => isFalse (by intro h; cases h)
    | .tuple _, .string => isFalse (by intro h; cases h)
    | .array _ _, .elem _ => isFalse (by intro h; cases h)
    | .array _ _, .mapping _ _ => isFalse (by intro h; cases h)
    | .array _ _, .contract _ => isFalse (by intro h; cases h)
    | .array _ _, .struct _ _ => isFalse (by intro h; cases h)
    | .array _ _, .tuple _ => isFalse (by intro h; cases h)
    | .array _ _, .dynamicArray _ => isFalse (by intro h; cases h)
    | .array _ _, .bytes => isFalse (by intro h; cases h)
    | .array _ _, .string => isFalse (by intro h; cases h)
    | .dynamicArray _, .elem _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .mapping _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .contract _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .struct _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .tuple _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .array _ _ => isFalse (by intro h; cases h)
    | .dynamicArray _, .bytes => isFalse (by intro h; cases h)
    | .dynamicArray _, .string => isFalse (by intro h; cases h)
    | .bytes, .elem _ => isFalse (by intro h; cases h)
    | .bytes, .mapping _ _ => isFalse (by intro h; cases h)
    | .bytes, .contract _ => isFalse (by intro h; cases h)
    | .bytes, .struct _ _ => isFalse (by intro h; cases h)
    | .bytes, .tuple _ => isFalse (by intro h; cases h)
    | .bytes, .array _ _ => isFalse (by intro h; cases h)
    | .bytes, .dynamicArray _ => isFalse (by intro h; cases h)
    | .bytes, .string => isFalse (by intro h; cases h)
    | .string, .elem _ => isFalse (by intro h; cases h)
    | .string, .mapping _ _ => isFalse (by intro h; cases h)
    | .string, .contract _ => isFalse (by intro h; cases h)
    | .string, .struct _ _ => isFalse (by intro h; cases h)
    | .string, .tuple _ => isFalse (by intro h; cases h)
    | .string, .array _ _ => isFalse (by intro h; cases h)
    | .string, .dynamicArray _ => isFalse (by intro h; cases h)
    | .string, .bytes => isFalse (by intro h; cases h)

  private def StorageType.decEqList : (as bs : List StorageType) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match StorageType.decEq a b, StorageType.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def StorageType.decEqNamedList : (as bs : List (Ident × StorageType)) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | (an, al) :: as, (bn, bl) :: bs =>
        match String.decEq an bn, StorageType.decEq al bl, StorageType.decEqNamedList as bs with
        | isTrue han, isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; cases han; rfl)
        | isFalse han, _, _ => isFalse (by intro h; cases h; exact han rfl)
        | _, isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq StorageType :=
  StorageType.decEq

inductive EnvVar where
  | caller
  | origin
  | callvalue
  | this
  | timestamp
  | selfbalance
  deriving DecidableEq, Repr, Inhabited

inductive UnaryOp where
  | not
  | neg
  | bitNot
  deriving DecidableEq, Repr, Inhabited

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
  deriving DecidableEq, Repr, Inhabited

/-- Whether a variable path is rooted in a memory **local** or **storage**. Resolved statically
    by the spec author / frontend, exactly as solc resolves the name. -/
inductive VarOrigin where
  | localVar
  | storage
  deriving DecidableEq, Repr, Inhabited

mutual

/- Expressions are intentionally lightweight for now. We are aiming for a meaningful
   subset of Solidity. -/
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
  /- `b[start:end]`: byte slice of dynamic bytes `b` over `[start, end)` -/
  | bytesSlice : Expr /- base -/ -> Expr /- start -/ -> Expr /- end -/ -> Expr
  | var : Ident -> Expr
  | env : EnvVar -> Expr
  /- for struct fields -/
  | field : Expr -> Ident -> Expr
  | storage : StorageRef -> Expr
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
     primitive is the same `ffi.KEC` the EVM's `KECCAK256` opcode uses, so equivalence reduces to
     equality of the hashed bytes. -/
  | keccak256 : Expr -> Expr
  /- `abi.encodePacked(e₁, …)`: the non-padded ("packed") ABI encoding of the listed values, as a
     dynamic `bytes`.  Each operand carries its (statically known) `ABIType`, which fixes its packed
     width (`uintN`→N/8 bytes, `bool`→1, `address`→20, `bytesN`→N, with no length prefixes). -/
  | abiEncodePacked : List (ABIType × Expr) -> Expr
  /- `addr.code.length` (EXTCODESIZE): the size in bytes of the code deployed at address `addr`.
     Matches `Ethereum.State.extCodeSize` — a non-existent account or an EOA (no code) has size 0.
     Used by ERC721 `safeTransferFrom`'s `to.code.length == 0` contract-detection guard. -/
  | extCodeSize : Expr -> Expr
  /- Fixed-size `bytesN` literal: the ABI type index (`n : Fin 32` ⇒ width `n+1`) and the bytes in
     Solidity order.  Models compile-time `bytesN` constants — hex `bytesN` literals, a function's
     `.selector` (`bytes4`), and `type(I).interfaceId` (`bytes4`) — all of which solc bakes as PUSH
     immediates.  Evaluates to `Value.fixedBytes n bs`; `==`/comparisons already act on `fixedBytes`. -/
  | fixedBytesLit : Fin 32 -> List UInt8 -> Expr

inductive StorageRefStep where
  | field : Ident -> StorageRefStep
  | mindex : Expr -> StorageRefStep
  | aindex : Expr -> StorageRefStep

structure StorageRef where /- TODO better name, since it can be a reference to locals or storage -/
  base : Ident
  steps : List StorageRefStep := []

/- Zoe: Shall we use StorageRef at the Expr level too instead of having field? -/

end

instance : Repr ByteArray where
  reprPrec b _ := repr b.data

deriving instance Repr for Expr
deriving instance Inhabited for Expr
deriving instance Repr for StorageRefStep
deriving instance Inhabited for StorageRefStep
deriving instance Repr for StorageRef
deriving instance Inhabited for StorageRef

-- The hand-written structural `DecidableEq` is an O(n²) match over `Expr`'s constructors; with the
-- `keccak256`/`abiEncodePacked` additions it exceeds the default heartbeat budget during the equation
-- compiler's `simp` pass, so the limit is raised for this block.
set_option maxHeartbeats 1000000 in
mutual
  private def Expr.decEq : (a b : Expr) -> Decidable (a = b)
    | .intLit x, .intLit y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .boolLit x, .boolLit y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .bytesLit x, .bytesLit y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .newBytes x, .newBytes y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .newArray tx x, .newArray ty y =>
        match (inferInstance : Decidable (tx = ty)), Expr.decEq x y with
        | isTrue ht, isTrue hx => isTrue (by cases ht; cases hx; rfl)
        | isFalse ht, _ => isFalse (by intro h'; cases h'; exact ht rfl)
        | _, isFalse hx => isFalse (by intro h'; cases h'; exact hx rfl)
    | .bytesSlice b1 s1 e1, .bytesSlice b2 s2 e2 =>
        match Expr.decEq b1 b2, Expr.decEq s1 s2, Expr.decEq e1 e2 with
        | isTrue hb, isTrue hs, isTrue he => isTrue (by cases hb; cases hs; cases he; rfl)
        | isFalse hb, _, _ => isFalse (by intro h'; cases h'; exact hb rfl)
        | _, isFalse hs, _ => isFalse (by intro h'; cases h'; exact hs rfl)
        | _, _, isFalse he => isFalse (by intro h'; cases h'; exact he rfl)
    | .var x, .var y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .env x, .env y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .field x fx, .field y fy =>
        match Expr.decEq x y, (inferInstance : Decidable (fx = fy)) with
        | isTrue hx, isTrue hf => isTrue (by subst y; subst fy; rfl)
        | isFalse hx, _ => isFalse (by intro h'; cases h'; exact hx rfl)
        | _, isFalse hf => isFalse (by intro h'; cases h'; exact hf rfl)
    | .storage x, .storage y =>
        match StorageRef.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .inRange tx x, .inRange ty y =>
        match (inferInstance : Decidable (tx = ty)), Expr.decEq x y with
        | isTrue ht, isTrue hx => isTrue (by cases ht; cases hx; rfl)
        | isFalse ht, _ => isFalse (by intro h'; cases h'; exact ht rfl)
        | _, isFalse hx => isFalse (by intro h'; cases h'; exact hx rfl)
    | .cast x tx, .cast y ty =>
        match Expr.decEq x y, (inferInstance : Decidable (tx = ty)) with
        | isTrue hx, isTrue ht => isTrue (by cases hx; cases ht; rfl)
        | isFalse hx, _ => isFalse (by intro h'; cases h'; exact hx rfl)
        | _, isFalse ht => isFalse (by intro h'; cases h'; exact ht rfl)
    | .addrOf x, .addrOf y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .unary ox x, .unary oy y =>
        match (inferInstance : Decidable (ox = oy)), Expr.decEq x y with
        | isTrue ho, isTrue hx => isTrue (by cases ho; cases hx; rfl)
        | isFalse ho, _ => isFalse (by intro h'; cases h'; exact ho rfl)
        | _, isFalse hx => isFalse (by intro h'; cases h'; exact hx rfl)
    | .binary ox lx rx, .binary oy ly ry =>
        match (inferInstance : Decidable (ox = oy)), Expr.decEq lx ly, Expr.decEq rx ry with
        | isTrue ho, isTrue hl, isTrue hr => isTrue (by cases ho; cases hl; cases hr; rfl)
        | isFalse ho, _, _ => isFalse (by intro h'; cases h'; exact ho rfl)
        | _, isFalse hl, _ => isFalse (by intro h'; cases h'; exact hl rfl)
        | _, _, isFalse hr => isFalse (by intro h'; cases h'; exact hr rfl)
    | .index bx ix, .index byx iy =>
        match Expr.decEq bx byx, Expr.decEq ix iy with
        | isTrue hb, isTrue hi => isTrue (by cases hb; cases hi; rfl)
        | isFalse hb, _ => isFalse (by intro h'; cases h'; exact hb rfl)
        | _, isFalse hi => isFalse (by intro h'; cases h'; exact hi rfl)
    | .ite cx tx fx, .ite cy ty fy =>
        match Expr.decEq cx cy, Expr.decEq tx ty, Expr.decEq fx fy with
        | isTrue hc, isTrue ht, isTrue hf => isTrue (by cases hc; cases ht; cases hf; rfl)
        | isFalse hc, _, _ => isFalse (by intro h'; cases h'; exact hc rfl)
        | _, isFalse ht, _ => isFalse (by intro h'; cases h'; exact ht rfl)
        | _, _, isFalse hf => isFalse (by intro h'; cases h'; exact hf rfl)
    | .arrayLength ox x, .arrayLength oy y =>
        match (inferInstance : Decidable (ox = oy)), StorageRef.decEq x y with
        | isTrue ho, isTrue hx => isTrue (by cases ho; cases hx; rfl)
        | isFalse ho, _ => isFalse (by intro h'; cases h'; exact ho rfl)
        | _, isFalse hx => isFalse (by intro h'; cases h'; exact hx rfl)
    | .newArray _ _, .intLit _ => isFalse (by intro h; cases h)
    | .newArray _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .newArray _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .newArray _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .newArray _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .var _ => isFalse (by intro h; cases h)
    | .newArray _ _, .env _ => isFalse (by intro h; cases h)
    | .newArray _ _, .field _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .storage _ => isFalse (by intro h; cases h)
    | .newArray _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .newArray _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .index _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .intLit _, .newArray _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .newArray _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .newArray _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .newArray _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .var _, .newArray _ _ => isFalse (by intro h; cases h)
    | .env _, .newArray _ _ => isFalse (by intro h; cases h)
    | .field _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .storage _, .newArray _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .newArray _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .index _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .intLit _, .boolLit _ => isFalse (by intro h; cases h)
    | .intLit _, .var _ => isFalse (by intro h; cases h)
    | .intLit _, .env _ => isFalse (by intro h; cases h)
    | .intLit _, .field _ _ => isFalse (by intro h; cases h)
    | .intLit _, .storage _ => isFalse (by intro h; cases h)
    | .intLit _, .inRange _ _ => isFalse (by intro h; cases h)
    | .intLit _, .cast _ _ => isFalse (by intro h; cases h)
    | .intLit _, .addrOf _ => isFalse (by intro h; cases h)
    | .intLit _, .unary _ _ => isFalse (by intro h; cases h)
    | .intLit _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .intLit _, .index _ _ => isFalse (by intro h; cases h)
    | .intLit _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .intLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .var _ => isFalse (by intro h; cases h)
    | .boolLit _, .env _ => isFalse (by intro h; cases h)
    | .boolLit _, .field _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .storage _ => isFalse (by intro h; cases h)
    | .boolLit _, .inRange _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .cast _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .addrOf _ => isFalse (by intro h; cases h)
    | .boolLit _, .unary _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .index _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .var _, .intLit _ => isFalse (by intro h; cases h)
    | .var _, .boolLit _ => isFalse (by intro h; cases h)
    | .var _, .env _ => isFalse (by intro h; cases h)
    | .var _, .field _ _ => isFalse (by intro h; cases h)
    | .var _, .storage _ => isFalse (by intro h; cases h)
    | .var _, .inRange _ _ => isFalse (by intro h; cases h)
    | .var _, .cast _ _ => isFalse (by intro h; cases h)
    | .var _, .addrOf _ => isFalse (by intro h; cases h)
    | .var _, .unary _ _ => isFalse (by intro h; cases h)
    | .var _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .var _, .index _ _ => isFalse (by intro h; cases h)
    | .var _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .env _, .intLit _ => isFalse (by intro h; cases h)
    | .env _, .boolLit _ => isFalse (by intro h; cases h)
    | .env _, .var _ => isFalse (by intro h; cases h)
    | .env _, .field _ _ => isFalse (by intro h; cases h)
    | .env _, .storage _ => isFalse (by intro h; cases h)
    | .env _, .inRange _ _ => isFalse (by intro h; cases h)
    | .env _, .cast _ _ => isFalse (by intro h; cases h)
    | .env _, .addrOf _ => isFalse (by intro h; cases h)
    | .env _, .unary _ _ => isFalse (by intro h; cases h)
    | .env _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .env _, .index _ _ => isFalse (by intro h; cases h)
    | .env _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .field _ _, .intLit _ => isFalse (by intro h; cases h)
    | .field _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .field _ _, .var _ => isFalse (by intro h; cases h)
    | .field _ _, .env _ => isFalse (by intro h; cases h)
    | .field _ _, .storage _ => isFalse (by intro h; cases h)
    | .field _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .field _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .field _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .field _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .field _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .field _ _, .index _ _ => isFalse (by intro h; cases h)
    | .field _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .storage _, .intLit _ => isFalse (by intro h; cases h)
    | .storage _, .boolLit _ => isFalse (by intro h; cases h)
    | .storage _, .var _ => isFalse (by intro h; cases h)
    | .storage _, .env _ => isFalse (by intro h; cases h)
    | .storage _, .field _ _ => isFalse (by intro h; cases h)
    | .storage _, .inRange _ _ => isFalse (by intro h; cases h)
    | .storage _, .cast _ _ => isFalse (by intro h; cases h)
    | .storage _, .addrOf _ => isFalse (by intro h; cases h)
    | .storage _, .unary _ _ => isFalse (by intro h; cases h)
    | .storage _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .storage _, .index _ _ => isFalse (by intro h; cases h)
    | .storage _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .intLit _ => isFalse (by intro h; cases h)
    | .inRange _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .inRange _ _, .var _ => isFalse (by intro h; cases h)
    | .inRange _ _, .env _ => isFalse (by intro h; cases h)
    | .inRange _ _, .field _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .storage _ => isFalse (by intro h; cases h)
    | .inRange _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .inRange _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .index _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .intLit _ => isFalse (by intro h; cases h)
    | .cast _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .cast _ _, .var _ => isFalse (by intro h; cases h)
    | .cast _ _, .env _ => isFalse (by intro h; cases h)
    | .cast _ _, .field _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .storage _ => isFalse (by intro h; cases h)
    | .cast _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .cast _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .index _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .intLit _ => isFalse (by intro h; cases h)
    | .addrOf _, .boolLit _ => isFalse (by intro h; cases h)
    | .addrOf _, .var _ => isFalse (by intro h; cases h)
    | .addrOf _, .env _ => isFalse (by intro h; cases h)
    | .addrOf _, .field _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .storage _ => isFalse (by intro h; cases h)
    | .addrOf _, .inRange _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .cast _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .unary _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .index _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .intLit _ => isFalse (by intro h; cases h)
    | .unary _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .unary _ _, .var _ => isFalse (by intro h; cases h)
    | .unary _ _, .env _ => isFalse (by intro h; cases h)
    | .unary _ _, .field _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .storage _ => isFalse (by intro h; cases h)
    | .unary _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .unary _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .index _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .intLit _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .var _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .env _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .field _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .storage _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .index _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .index _ _, .intLit _ => isFalse (by intro h; cases h)
    | .index _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .index _ _, .var _ => isFalse (by intro h; cases h)
    | .index _ _, .env _ => isFalse (by intro h; cases h)
    | .index _ _, .field _ _ => isFalse (by intro h; cases h)
    | .index _ _, .storage _ => isFalse (by intro h; cases h)
    | .index _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .index _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .index _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .index _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .index _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .index _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .intLit _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .var _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .env _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .field _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .storage _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .index _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .intLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .boolLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .var _ => isFalse (by intro h; cases h)
    | .bytesLit _, .env _ => isFalse (by intro h; cases h)
    | .bytesLit _, .field _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .storage _ => isFalse (by intro h; cases h)
    | .bytesLit _, .inRange _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .cast _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .addrOf _ => isFalse (by intro h; cases h)
    | .bytesLit _, .unary _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .index _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .newBytes _ => isFalse (by intro h; cases h)
    | .intLit _, .bytesLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .bytesLit _ => isFalse (by intro h; cases h)
    | .var _, .bytesLit _ => isFalse (by intro h; cases h)
    | .env _, .bytesLit _ => isFalse (by intro h; cases h)
    | .field _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .storage _, .bytesLit _ => isFalse (by intro h; cases h)
    | .inRange _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .cast _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .addrOf _, .bytesLit _ => isFalse (by intro h; cases h)
    | .unary _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .index _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .newBytes _, .intLit _ => isFalse (by intro h; cases h)
    | .newBytes _, .boolLit _ => isFalse (by intro h; cases h)
    | .newBytes _, .var _ => isFalse (by intro h; cases h)
    | .newBytes _, .env _ => isFalse (by intro h; cases h)
    | .newBytes _, .field _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .storage _ => isFalse (by intro h; cases h)
    | .newBytes _, .inRange _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .cast _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .addrOf _ => isFalse (by intro h; cases h)
    | .newBytes _, .unary _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .index _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .bytesLit _ => isFalse (by intro h; cases h)
    | .intLit _, .newBytes _ => isFalse (by intro h; cases h)
    | .boolLit _, .newBytes _ => isFalse (by intro h; cases h)
    | .var _, .newBytes _ => isFalse (by intro h; cases h)
    | .env _, .newBytes _ => isFalse (by intro h; cases h)
    | .field _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .storage _, .newBytes _ => isFalse (by intro h; cases h)
    | .inRange _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .cast _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .addrOf _, .newBytes _ => isFalse (by intro h; cases h)
    | .unary _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .index _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .intLit _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .var _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .env _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .field _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .storage _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .index _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .intLit _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .var _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .env _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .field _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .storage _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .index _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .intLit _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .var _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .env _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .field _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .storage _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .index _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .intLit _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .boolLit _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .bytesLit _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .newBytes _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .var _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .env _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .field _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .storage _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .addrOf _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .index _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .structLit nx fx, .structLit ny fy =>
        match (inferInstance : Decidable (nx = ny)), Expr.decEqNamedList fx fy with
        | isTrue hn, isTrue hf => isTrue (by cases hn; cases hf; rfl)
        | isFalse hn, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse hf => isFalse (by intro h; cases h; exact hf rfl)
    | .arrayLit xs, .arrayLit ys =>
        match Expr.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .structLit _ _, .intLit _ => isFalse (by intro h; cases h)
    | .intLit _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .newBytes _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .var _ => isFalse (by intro h; cases h)
    | .var _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .env _ => isFalse (by intro h; cases h)
    | .env _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .field _ _ => isFalse (by intro h; cases h)
    | .field _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .storage _ => isFalse (by intro h; cases h)
    | .storage _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .addrOf _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .index _ _ => isFalse (by intro h; cases h)
    | .index _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .arrayLit _, .intLit _ => isFalse (by intro h; cases h)
    | .intLit _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .boolLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .bytesLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .newBytes _ => isFalse (by intro h; cases h)
    | .newBytes _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .newArray _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .var _ => isFalse (by intro h; cases h)
    | .var _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .env _ => isFalse (by intro h; cases h)
    | .env _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .field _ _ => isFalse (by intro h; cases h)
    | .field _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .storage _ => isFalse (by intro h; cases h)
    | .storage _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .inRange _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .cast _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .addrOf _ => isFalse (by intro h; cases h)
    | .addrOf _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .unary _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .index _ _ => isFalse (by intro h; cases h)
    | .index _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .structLit _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .structLit _ _ => isFalse (by intro h; cases h)
    | .tupleLit xs, .tupleLit ys =>
        match Expr.decEqList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .tupleLit _, .intLit _ => isFalse (by intro h; cases h)
    | .intLit _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .boolLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .bytesLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .newBytes _ => isFalse (by intro h; cases h)
    | .newBytes _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .newArray _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .var _ => isFalse (by intro h; cases h)
    | .var _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .env _ => isFalse (by intro h; cases h)
    | .env _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .field _ _ => isFalse (by intro h; cases h)
    | .field _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .storage _ => isFalse (by intro h; cases h)
    | .storage _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .inRange _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .cast _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .addrOf _ => isFalse (by intro h; cases h)
    | .addrOf _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .unary _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .index _ _ => isFalse (by intro h; cases h)
    | .index _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .keccak256 x, .keccak256 y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .keccak256 _, .intLit _ => isFalse (by intro h; cases h)
    | .intLit _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .boolLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .bytesLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .newBytes _ => isFalse (by intro h; cases h)
    | .newBytes _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .newArray _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .var _ => isFalse (by intro h; cases h)
    | .var _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .env _ => isFalse (by intro h; cases h)
    | .env _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .field _ _ => isFalse (by intro h; cases h)
    | .field _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .storage _ => isFalse (by intro h; cases h)
    | .storage _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .inRange _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .cast _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .addrOf _ => isFalse (by intro h; cases h)
    | .addrOf _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .unary _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .index _ _ => isFalse (by intro h; cases h)
    | .index _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .keccak256 _ => isFalse (by intro h; cases h)
    | .abiEncodePacked xs, .abiEncodePacked ys =>
        match Expr.decEqTypedList xs ys with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .abiEncodePacked _, .intLit _ => isFalse (by intro h; cases h)
    | .intLit _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .boolLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .bytesLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .newBytes _ => isFalse (by intro h; cases h)
    | .newBytes _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .newArray _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .var _ => isFalse (by intro h; cases h)
    | .var _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .env _ => isFalse (by intro h; cases h)
    | .env _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .field _ _ => isFalse (by intro h; cases h)
    | .field _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .storage _ => isFalse (by intro h; cases h)
    | .storage _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .inRange _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .cast _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .addrOf _ => isFalse (by intro h; cases h)
    | .addrOf _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .unary _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .index _ _ => isFalse (by intro h; cases h)
    | .index _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .extCodeSize x, .extCodeSize y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .fixedBytesLit nx bx, .fixedBytesLit ny byy =>
        match (inferInstance : Decidable (nx = ny)), (inferInstance : Decidable (bx = byy)) with
        | isTrue hn, isTrue hb => isTrue (by cases hn; cases hb; rfl)
        | isFalse hn, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
    | .extCodeSize _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .intLit _ => isFalse (by intro h; cases h)
    | .intLit _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .boolLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .bytesLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .newBytes _ => isFalse (by intro h; cases h)
    | .newBytes _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .newArray _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .var _ => isFalse (by intro h; cases h)
    | .var _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .env _ => isFalse (by intro h; cases h)
    | .env _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .field _ _ => isFalse (by intro h; cases h)
    | .field _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .storage _ => isFalse (by intro h; cases h)
    | .storage _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .inRange _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .cast _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .addrOf _ => isFalse (by intro h; cases h)
    | .addrOf _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .unary _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .index _ _ => isFalse (by intro h; cases h)
    | .index _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .extCodeSize _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .extCodeSize _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .intLit _ => isFalse (by intro h; cases h)
    | .intLit _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .boolLit _ => isFalse (by intro h; cases h)
    | .boolLit _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .bytesLit _ => isFalse (by intro h; cases h)
    | .bytesLit _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .newBytes _ => isFalse (by intro h; cases h)
    | .newBytes _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .newArray _ _ => isFalse (by intro h; cases h)
    | .newArray _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .structLit _ _ => isFalse (by intro h; cases h)
    | .structLit _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .arrayLit _ => isFalse (by intro h; cases h)
    | .arrayLit _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .tupleLit _ => isFalse (by intro h; cases h)
    | .tupleLit _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .bytesSlice _ _ _ => isFalse (by intro h; cases h)
    | .bytesSlice _ _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .var _ => isFalse (by intro h; cases h)
    | .var _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .env _ => isFalse (by intro h; cases h)
    | .env _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .field _ _ => isFalse (by intro h; cases h)
    | .field _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .storage _ => isFalse (by intro h; cases h)
    | .storage _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .inRange _ _ => isFalse (by intro h; cases h)
    | .inRange _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .cast _ _ => isFalse (by intro h; cases h)
    | .cast _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .addrOf _ => isFalse (by intro h; cases h)
    | .addrOf _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .unary _ _ => isFalse (by intro h; cases h)
    | .unary _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .binary _ _ _ => isFalse (by intro h; cases h)
    | .binary _ _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .index _ _ => isFalse (by intro h; cases h)
    | .index _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .arrayLength _ _ => isFalse (by intro h; cases h)
    | .arrayLength _ _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .keccak256 _ => isFalse (by intro h; cases h)
    | .keccak256 _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)
    | .fixedBytesLit _ _, .abiEncodePacked _ => isFalse (by intro h; cases h)
    | .abiEncodePacked _, .fixedBytesLit _ _ => isFalse (by intro h; cases h)

  private def Expr.decEqList : (as bs : List Expr) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match Expr.decEq a b, Expr.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def Expr.decEqNamedList : (as bs : List (Ident × Expr)) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | (nx, ex) :: as, (ny, ey) :: bs =>
        match (inferInstance : Decidable (nx = ny)), Expr.decEq ex ey, Expr.decEqNamedList as bs with
        | isTrue hn, isTrue he, isTrue hs => isTrue (by cases hn; cases he; cases hs; rfl)
        | isFalse hn, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse he, _ => isFalse (by intro h; cases h; exact he rfl)
        | _, _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def Expr.decEqTypedList : (as bs : List (ABIType × Expr)) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | (tx, ex) :: as, (ty, ey) :: bs =>
        match (inferInstance : Decidable (tx = ty)), Expr.decEq ex ey, Expr.decEqTypedList as bs with
        | isTrue ht, isTrue he, isTrue hs => isTrue (by cases ht; cases he; cases hs; rfl)
        | isFalse ht, _, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, isFalse he, _ => isFalse (by intro h; cases h; exact he rfl)
        | _, _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)

  private def StorageRefStep.decEq : (a b : StorageRefStep) -> Decidable (a = b)
    | .field x, .field y =>
        match (inferInstance : Decidable (x = y)) with
        | isTrue h => isTrue (by subst y; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .mindex x, .mindex y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .aindex x, .aindex y =>
        match Expr.decEq x y with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .field _, .mindex _ => isFalse (by intro h; cases h)
    | .field _, .aindex _ => isFalse (by intro h; cases h)
    | .mindex _, .field _ => isFalse (by intro h; cases h)
    | .mindex _, .aindex _ => isFalse (by intro h; cases h)
    | .aindex _, .field _ => isFalse (by intro h; cases h)
    | .aindex _, .mindex _ => isFalse (by intro h; cases h)

  private def StorageRef.decEq : (a b : StorageRef) -> Decidable (a = b)
    | ⟨base, steps⟩, ⟨base', steps'⟩ =>
        match (inferInstance : Decidable (base = base')), StorageRefStep.decEqList steps steps' with
        | isTrue hb, isTrue hs => isTrue (by cases hb; cases hs; rfl)
        | isFalse hb, _ => isFalse (by intro h; cases h; exact hb rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)

  private def StorageRefStep.decEqList : (as bs : List StorageRefStep) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match StorageRefStep.decEq a b, StorageRefStep.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Expr :=
  Expr.decEq

instance : DecidableEq StorageRefStep :=
  StorageRefStep.decEq

instance : DecidableEq StorageRef :=
  StorageRef.decEq

namespace StorageRef

def var (name : Ident) : StorageRef :=
  { base := name }

end StorageRef

inductive AssignRhs where
  | expr : Expr -> AssignRhs
  -- Do we want non-determinism?
  -- | havoc
  deriving DecidableEq, Repr, Inhabited

inductive Stmt where
  /- local variable -/
  | letDecl : Ident -> Option ABIType -> Expr -> Stmt
  /- local storage alias: `T storage x = ref`; stores an evaluated storage pointer in locals -/
  | letStorage : Ident -> StorageRef -> Stmt
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
  /- constructor call -/
  | new : Ident -> Expr /- ETH to send -/ -> List Expr -> Ident /- return value binder -/ -> Stmt
  /- internal and external call results are explicitly let-bound -/
  | internalCall : Ident -> List Expr -> Ident /- return value binder -/ -> Stmt
  | externalCall : Expr -> Ident -> Expr /- ETH to send -/ -> List Expr -> Ident /- return value binder -/ -> Stmt
  /- low-level `target.call{value: v}(data)`: raw call, binds a success `bool` to `okVar`,
     returndata dropped, callee revert does NOT propagate -/
  | lowLevelCall : Expr /- target -/ -> Expr /- ETH to send -/ -> Expr /- calldata bytes -/ -> Ident /- success binder -/ -> Ident /- raw returndata binder -/ -> Stmt
  /- `try recv.name{value}(args) returns (retVar) { onSuccess } catch Error(string) { onCatch }`.
     Only `Error(string)`-reason callee reverts are caught; other reverts propagate.  `retVar` is
     bound only within `onSuccess`. -/
  | checkedCall : Expr /- receiver -/ -> Ident /- name -/ -> Expr /- ETH -/ -> List Expr /- args -/ -> Ident /- decoded return, scoped to onSuccess -/ -> List Stmt /- onSuccess -/ -> Ident /- raw revert bytes, scoped to onFail -/ -> List Stmt /- onFail -/ -> Stmt
  | return : Expr -> Stmt
  | break : Stmt
  | continue : Stmt
  /- `arr.push(v?)`: grow a dynamic storage array by one.  `some v` appends scalar `v`; `none` is a
     grow-only push (structured elements — the new slots are zero, fields set by later writes). -/
  | push : StorageRef -> Option Expr -> Stmt
  /- `arr.pop()`: remove the last element of a dynamic storage array (reverts if empty),
     clearing the slot and shrinking its length by one -/
  | pop : StorageRef -> Stmt
  /- `delete x`: reset the storage at `x` to its zero value (recursively, per its type) -/
  | delete : StorageRef -> Stmt
  deriving Repr, Inhabited


mutual
  private def Stmt.decEq : (a b : Stmt) -> Decidable (a = b)
    | .letDecl nx tx ex, .letDecl ny ty ey =>
        match (inferInstance : Decidable (nx = ny)), (inferInstance : Decidable (tx = ty)), Expr.decEq ex ey with
        | isTrue hn, isTrue ht, isTrue he => isTrue (by cases hn; cases ht; cases he; rfl)
        | isFalse hn, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse ht, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, _, isFalse he => isFalse (by intro h; cases h; exact he rfl)
    | .letStorage nx rx, .letStorage ny ry =>
        match (inferInstance : Decidable (nx = ny)), StorageRef.decEq rx ry with
        | isTrue hn, isTrue hr => isTrue (by cases hn; cases hr; rfl)
        | isFalse hn, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .assign ox sx ex, .assign oy sy ey =>
        match (inferInstance : Decidable (ox = oy)), StorageRef.decEq sx sy, Expr.decEq ex ey with
        | isTrue ho, isTrue hs, isTrue he => isTrue (by cases ho; cases hs; cases he; rfl)
        | isFalse ho, _, _ => isFalse (by intro h; cases h; exact ho rfl)
        | _, isFalse hs, _ => isFalse (by intro h; cases h; exact hs rfl)
        | _, _, isFalse he => isFalse (by intro h; cases h; exact he rfl)
    | .require ex, .require ey =>
        match Expr.decEq ex ey with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .while cx bx, .while cy bodyY =>
        match Expr.decEq cx cy, Stmt.decEqList bx bodyY with
        | isTrue hc, isTrue hb => isTrue (by cases hc; cases hb; rfl)
        | isFalse hc, _ => isFalse (by intro h; cases h; exact hc rfl)
        | _, isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
    | .ite cx tx ex, .ite cy ty ey =>
        match Expr.decEq cx cy, Stmt.decEqList tx ty, Stmt.decEqList ex ey with
        | isTrue hc, isTrue ht, isTrue he => isTrue (by cases hc; cases ht; cases he; rfl)
        | isFalse hc, _, _ => isFalse (by intro h; cases h; exact hc rfl)
        | _, isFalse ht, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, _, isFalse he => isFalse (by intro h; cases h; exact he rfl)
    | .new nx vx ax rx, .new ny vy ay ry =>
        match (inferInstance : Decidable (nx = ny)), Expr.decEq vx vy, (inferInstance : Decidable (ax = ay)), (inferInstance : Decidable (rx = ry)) with
        | isTrue hn, isTrue hv, isTrue ha, isTrue hr => isTrue (by cases hn; cases hv; cases ha; cases hr; rfl)
        | isFalse hn, _, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse hv, _, _ => isFalse (by intro h; cases h; exact hv rfl)
        | _, _, isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, _, isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .internalCall nx ax rx, .internalCall ny ay ry =>
        match (inferInstance : Decidable (nx = ny)), (inferInstance : Decidable (ax = ay)), (inferInstance : Decidable (rx = ry)) with
        | isTrue hn, isTrue ha, isTrue hr => isTrue (by cases hn; cases ha; cases hr; rfl)
        | isFalse hn, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .externalCall tx nx vx ax rx, .externalCall ty ny vy ay ry =>
        match Expr.decEq tx ty, (inferInstance : Decidable (nx = ny)), Expr.decEq vx vy, (inferInstance : Decidable (ax = ay)), (inferInstance : Decidable (rx = ry)) with
        | isTrue ht, isTrue hn, isTrue hv, isTrue ha, isTrue hr => isTrue (by cases ht; cases hn; cases hv; cases ha; cases hr; rfl)
        | isFalse ht, _, _, _, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, isFalse hn, _, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, _, isFalse hv, _, _ => isFalse (by intro h; cases h; exact hv rfl)
        | _, _, _, isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, _, _, isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .lowLevelCall tx vx cx ox dx, .lowLevelCall ty vy cy oy dy =>
        match Expr.decEq tx ty, Expr.decEq vx vy, Expr.decEq cx cy, (inferInstance : Decidable (ox = oy)), (inferInstance : Decidable (dx = dy)) with
        | isTrue ht, isTrue hv, isTrue hc, isTrue ho, isTrue hd => isTrue (by cases ht; cases hv; cases hc; cases ho; cases hd; rfl)
        | isFalse ht, _, _, _, _ => isFalse (by intro h; cases h; exact ht rfl)
        | _, isFalse hv, _, _, _ => isFalse (by intro h; cases h; exact hv rfl)
        | _, _, isFalse hc, _, _ => isFalse (by intro h; cases h; exact hc rfl)
        | _, _, _, isFalse ho, _ => isFalse (by intro h; cases h; exact ho rfl)
        | _, _, _, _, isFalse hd => isFalse (by intro h; cases h; exact hd rfl)
    | .checkedCall rx nx vx ax retx sx ex cx, .checkedCall ry ny vy ay rety sy ey cy =>
        match Expr.decEq rx ry, (inferInstance : Decidable (nx = ny)), Expr.decEq vx vy,
            (inferInstance : Decidable (ax = ay)), (inferInstance : Decidable (retx = rety)),
            Stmt.decEqList sx sy, (inferInstance : Decidable (ex = ey)), Stmt.decEqList cx cy with
        | isTrue hr, isTrue hn, isTrue hv, isTrue ha, isTrue hret, isTrue hs, isTrue he, isTrue hc =>
            isTrue (by cases hr; cases hn; cases hv; cases ha; cases hret; cases hs; cases he; cases hc; rfl)
        | isFalse hr, _, _, _, _, _, _, _ => isFalse (by intro h; cases h; exact hr rfl)
        | _, isFalse hn, _, _, _, _, _, _ => isFalse (by intro h; cases h; exact hn rfl)
        | _, _, isFalse hv, _, _, _, _, _ => isFalse (by intro h; cases h; exact hv rfl)
        | _, _, _, isFalse ha, _, _, _, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, _, _, _, isFalse hret, _, _, _ => isFalse (by intro h; cases h; exact hret rfl)
        | _, _, _, _, _, isFalse hs, _, _ => isFalse (by intro h; cases h; exact hs rfl)
        | _, _, _, _, _, _, isFalse he, _ => isFalse (by intro h; cases h; exact he rfl)
        | _, _, _, _, _, _, _, isFalse hc => isFalse (by intro h; cases h; exact hc rfl)
    | .return ex, .return ey =>
        match Expr.decEq ex ey with
        | isTrue h => isTrue (by cases h; rfl)
        | isFalse h => isFalse (by intro h'; cases h'; exact h rfl)
    | .break, .break => isTrue rfl
    | .continue, .continue => isTrue rfl
    | .letStorage _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .require _ => isFalse (by intro h; cases h)
    | .require _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .while _ _ => isFalse (by intro h; cases h)
    | .while _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .return _ => isFalse (by intro h; cases h)
    | .return _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .break => isFalse (by intro h; cases h)
    | .break, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .continue => isFalse (by intro h; cases h)
    | .continue, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .require _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .return _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .break => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .continue => isFalse (by intro h; cases h)
    | .assign _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .require _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .return _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .break => isFalse (by intro h; cases h)
    | .assign _ _ _, .continue => isFalse (by intro h; cases h)
    | .require _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .require _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .require _, .while _ _ => isFalse (by intro h; cases h)
    | .require _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .require _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .require _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .require _, .return _ => isFalse (by intro h; cases h)
    | .require _, .break => isFalse (by intro h; cases h)
    | .require _, .continue => isFalse (by intro h; cases h)
    | .while _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .require _ => isFalse (by intro h; cases h)
    | .while _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .return _ => isFalse (by intro h; cases h)
    | .while _ _, .break => isFalse (by intro h; cases h)
    | .while _ _, .continue => isFalse (by intro h; cases h)
    | .new _ _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .require _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .return _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .break => isFalse (by intro h; cases h)
    | .new _ _ _ _, .continue => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .require _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .return _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .break => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .continue => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .require _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .return _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .break => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .continue => isFalse (by intro h; cases h)
    | .return _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .return _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .return _, .require _ => isFalse (by intro h; cases h)
    | .return _, .while _ _ => isFalse (by intro h; cases h)
    | .return _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .return _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .return _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .return _, .break => isFalse (by intro h; cases h)
    | .return _, .continue => isFalse (by intro h; cases h)
    | .break, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .break, .assign _ _ _ => isFalse (by intro h; cases h)
    | .break, .require _ => isFalse (by intro h; cases h)
    | .break, .while _ _ => isFalse (by intro h; cases h)
    | .break, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .break, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .break, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .break, .return _ => isFalse (by intro h; cases h)
    | .break, .continue => isFalse (by intro h; cases h)
    | .continue, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .continue, .assign _ _ _ => isFalse (by intro h; cases h)
    | .continue, .require _ => isFalse (by intro h; cases h)
    | .continue, .while _ _ => isFalse (by intro h; cases h)
    | .continue, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .continue, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .continue, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .continue, .return _ => isFalse (by intro h; cases h)
    | .continue, .break => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .require _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .return _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .break, .ite _ _ _ => isFalse (by intro h; cases h)
    | .continue, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .require _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .return _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .break => isFalse (by intro h; cases h)
    | .ite _ _ _, .continue => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .require _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .return _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .break => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .continue => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .require _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .return _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .break, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .continue, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .require _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .return _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .break => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .continue => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .require _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .while _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .return _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .break, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .continue, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .push rx vx, .push ry vy =>
        match StorageRef.decEq rx ry, (inferInstance : Decidable (vx = vy)) with
        | isTrue hr, isTrue hv => isTrue (by cases hr; cases hv; rfl)
        | isFalse hr, _ => isFalse (by intro h; cases h; exact hr rfl)
        | _, isFalse hv => isFalse (by intro h; cases h; exact hv rfl)
    | .pop rx, .pop ry =>
        match StorageRef.decEq rx ry with
        | isTrue hr => isTrue (by cases hr; rfl)
        | isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .delete rx, .delete ry =>
        match StorageRef.decEq rx ry with
        | isTrue hr => isTrue (by cases hr; rfl)
        | isFalse hr => isFalse (by intro h; cases h; exact hr rfl)
    | .delete _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .require _ => isFalse (by intro h; cases h)
    | .require _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .while _ _ => isFalse (by intro h; cases h)
    | .while _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .return _ => isFalse (by intro h; cases h)
    | .return _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .break => isFalse (by intro h; cases h)
    | .break, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .continue => isFalse (by intro h; cases h)
    | .continue, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .delete _ => isFalse (by intro h; cases h)
    | .push _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .require _ => isFalse (by intro h; cases h)
    | .require _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .while _ _ => isFalse (by intro h; cases h)
    | .while _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .return _ => isFalse (by intro h; cases h)
    | .return _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .break => isFalse (by intro h; cases h)
    | .break, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .continue => isFalse (by intro h; cases h)
    | .continue, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .push _ _ => isFalse (by intro h; cases h)
    | .pop _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .require _ => isFalse (by intro h; cases h)
    | .require _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .while _ _ => isFalse (by intro h; cases h)
    | .while _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .return _ => isFalse (by intro h; cases h)
    | .return _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .break => isFalse (by intro h; cases h)
    | .break, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .continue => isFalse (by intro h; cases h)
    | .continue, .pop _ => isFalse (by intro h; cases h)
    | .for ix cx px bx, .for iy cy py by_ =>
        match Stmt.decEqList ix iy, Expr.decEq cx cy, Stmt.decEqList px py, Stmt.decEqList bx by_ with
        | isTrue hi, isTrue hc, isTrue hp, isTrue hb => isTrue (by cases hi; cases hc; cases hp; cases hb; rfl)
        | isFalse hi, _, _, _ => isFalse (by intro h; cases h; exact hi rfl)
        | _, isFalse hc, _, _ => isFalse (by intro h; cases h; exact hc rfl)
        | _, _, isFalse hp, _ => isFalse (by intro h; cases h; exact hp rfl)
        | _, _, _, isFalse hb => isFalse (by intro h; cases h; exact hb rfl)
    | .for _ _ _ _, .letDecl _ _ _ => isFalse (by intro h; cases h)
    | .letDecl _ _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .letStorage _ _ => isFalse (by intro h; cases h)
    | .letStorage _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .assign _ _ _ => isFalse (by intro h; cases h)
    | .assign _ _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .require _ => isFalse (by intro h; cases h)
    | .require _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .while _ _ => isFalse (by intro h; cases h)
    | .while _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .ite _ _ _ => isFalse (by intro h; cases h)
    | .ite _ _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .new _ _ _ _ => isFalse (by intro h; cases h)
    | .new _ _ _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .internalCall _ _ _ => isFalse (by intro h; cases h)
    | .internalCall _ _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .externalCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .externalCall _ _ _ _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .lowLevelCall _ _ _ _ _ => isFalse (by intro h; cases h)
    | .lowLevelCall _ _ _ _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .checkedCall _ _ _ _ _ _ _ _ => isFalse (by intro h; cases h)
    | .checkedCall _ _ _ _ _ _ _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .return _ => isFalse (by intro h; cases h)
    | .return _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .break => isFalse (by intro h; cases h)
    | .break, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .continue => isFalse (by intro h; cases h)
    | .continue, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .push _ _ => isFalse (by intro h; cases h)
    | .push _ _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .pop _ => isFalse (by intro h; cases h)
    | .pop _, .for _ _ _ _ => isFalse (by intro h; cases h)
    | .for _ _ _ _, .delete _ => isFalse (by intro h; cases h)
    | .delete _, .for _ _ _ _ => isFalse (by intro h; cases h)

  private def Stmt.decEqList : (as bs : List Stmt) -> Decidable (as = bs)
    | [], [] => isTrue rfl
    | a :: as, b :: bs =>
        match Stmt.decEq a b, Stmt.decEqList as bs with
        | isTrue ha, isTrue hs => isTrue (by cases ha; cases hs; rfl)
        | isFalse ha, _ => isFalse (by intro h; cases h; exact ha rfl)
        | _, isFalse hs => isFalse (by intro h; cases h; exact hs rfl)
    | [], _ :: _ => isFalse (by intro h; cases h)
    | _ :: _, [] => isFalse (by intro h; cases h)
end

instance : DecidableEq Stmt :=
  Stmt.decEq

abbrev Body := List Stmt

structure Param where
  name : Ident
  ty : ABI.ABIType
  deriving DecidableEq, Repr, Inhabited

structure StorageDecl where
  name : Ident
  ty : StorageType
  deriving DecidableEq, Repr, Inhabited

structure ConstructorDecl where
  params : List Param
  body : List Stmt
  deriving DecidableEq, Repr, Inhabited

-- Currently this covers storage structs
-- The ABI technically has no structs,
-- Solidity implements call-parameter structs through ABI tuples
structure StructDecl where
  name : Ident
  fields : List StorageDecl
  deriving DecidableEq, Repr, Inhabited

structure FunctionDecl where
  name : Ident
  params : List Param
  returnType : Option ABIType := none
  body : List Stmt
  deriving DecidableEq, Repr, Inhabited

structure TransitionDecl where
  name : Ident
  params : List Param
  returnType : Option ABIType := none
  body : List Stmt
  deriving DecidableEq, Repr, Inhabited

structure ContractDecl where
  name : Ident
  storage : List StorageDecl
  ctor : ConstructorDecl
  structs : List StructDecl := [] -- Maybe these should not be per-contract. Zoe: if we are inlining them anyway, do we still need this?
  functions : List FunctionDecl := []
  transitions : List TransitionDecl := []
  deriving DecidableEq, Repr, Inhabited

abbrev Program := List ContractDecl

end Solm
