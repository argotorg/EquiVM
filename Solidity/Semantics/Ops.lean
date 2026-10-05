import Solidity.Semantics.Types
import Solm.Semantics.ValueOps

/-!
# Pure helpers shared by the relational rules and the interpreter

Every rule premise that is not a sub-derivation is an equation on one of these functions, so the
interpreter is the rules read as a program.  `Op α` (`= Option (Except Panic α)`) is the common
result shape: `none` means the program is ill-formed (no rule applies), `throw p` a `Panic`.
-/

namespace Solidity

open ABI

abbrev Op := ExceptT Panic Option

def Op.stuck {α} : Op α := ExceptT.mk none
def Op.ofOpt {α} (o : Option α) : Op α := ExceptT.mk (o.map .ok)
def Op.panic {α} (p : Panic) : Op α := ExceptT.mk (some (.error p))

/-! ## Environment -/

def wordNat (n : Nat) : Value := .uint ⟨256, by decide⟩ ((EVM.Word.ofNat n).toNat)

def balanceOf (evm : EVM.State) (a : EVM.Address) : Nat :=
  match evm.lookupAccount a with
  | some acc => acc.balance.toNat
  | none => 0

/-- `msg.*`, `block.*`, `tx.*` members (all but `msg.data`, which allocates). -/
def envMember (m : Machine) (obj member : Ident) : Option Value :=
  let ee := m.evm.executionEnv
  match obj, member with
  | "msg", "sender" => some (.address ee.source)
  | "msg", "value" => some (wordNat ee.weiValue.toNat)
  | "msg", "sig" =>
    let b := ee.calldata.toList.take 4
    some (.fixedBytes ⟨3, by decide⟩ (b ++ List.replicate (4 - b.length) 0))
  | "tx", "origin" => some (.address ee.sender)
  | "tx", "gasprice" => some (wordNat ee.gasPrice)
  | "block", "timestamp" => some (wordNat ee.header.timestamp)
  | "block", "number" => some (wordNat ee.header.number)
  | "block", "chainid" => some (wordNat Ethereum.chainId)
  | "block", "coinbase" => some (.address ee.header.beneficiary)
  | "block", "gaslimit" => some (wordNat ee.header.gasLimit)
  | "block", "prevrandao" => some (wordNat ee.header.prevRandao.toNat)
  -- since the Paris fork `difficulty` is the same opcode as `prevrandao`
  | "block", "difficulty" => some (wordNat ee.header.prevRandao.toNat)
  | "block", "basefee" => some (wordNat ee.header.baseFeePerGas)
  | _, _ => none

/-! ## Keys and truth values -/

def keyOf : Value → Option Solm.KeyValue
  | .uint _ n => some (.int n)
  | .sint _ i => some (.int i)
  | .literal i _ => some (.int i)
  | .bool b => some (.bool b)
  | .address a => some (.address a)
  | .contract _ a => some (.address a)
  | .fixedBytes n bs => some (.fixedBytes n bs)
  | .enum _ _ i => some (.int i)
  | .wrapped _ _ v => keyOf v
  | _ => none

def toBool : Value → Option Bool
  | .bool b => some b
  | _ => none

/-- Validate a raw calldata word for its type when it is read (solc's validator: a word that is
    not canonical reverts with empty data).  A value type validates as its underlying type, an
    enum must be below its member count, a contract is an `address`. -/
def validateRaw (env : TypeEnv) (ty : Ty) (w : Nat) : Except ByteArray Value :=
  match ty with
  | .user q n =>
    match env.valueType? q n with
    | some t =>
      match validateWord t.underlying w with
      | some u => .ok (.wrapped q n u)
      | none => .error ByteArray.empty
    | none =>
      match env.enum? q n with
      | some e => if w < e.members.length then .ok (.enum q n w) else .error ByteArray.empty
      | none =>
        if (env.contractKind? n).isSome && w < 2 ^ 160 then .ok (.contract n (EVM.address w))
        else .error ByteArray.empty
  | ty =>
    match validateWord ty w with
    | some v => .ok v
    | none => .error ByteArray.empty

/-- A raw calldata word copied to memory: solc's cleanup (`cleanWord`); an enum out of range is
    `Panic(0x21)` (solc checks it when the copy is read), a contract is masked to an address. -/
def cleanRaw (env : TypeEnv) (ty : Ty) (w : Nat) : Op Value :=
  match ty with
  | .user q n =>
    match env.valueType? q n with
    | some t => Op.ofOpt ((cleanWord t.underlying w).map (.wrapped q n))
    | none =>
      match env.enum? q n with
      | some e => if w < e.members.length then pure (.enum q n w) else Op.panic .enumRange
      | none =>
        if (env.contractKind? n).isSome then pure (.contract n (EVM.address (w % 2 ^ 160))) else Op.stuck
  | ty => Op.ofOpt (cleanWord ty w)

/-! ## Literal adoption and operators -/

/-- A literal meeting a typed integer takes that type (must fit). -/
def adopt (t : IntTy) : Value → Option Value
  | .literal i _ => if t.inRange i then some (mkInt t i) else none
  | v => some v

/-- The type of an operation between an operand of type `t` and a number literal that does not fit
    `t`: the literal's mobile type, when `t` converts to it implicitly (solc's common type; e.g.
    `uint8 * 300` is `uint16` arithmetic). -/
def literalWiden (t : IntTy) (x : Int) : Option IntTy :=
  (mobileType x).bind fun mt => if implicitIntConv t mt then some mt else none

/-- Integer operands unified to a common type (`(type, a, b)`); literal–literal stays exact. -/
def unifyInts (a b : Value) : Option (Option IntTy × Int × Int) :=
  match a, b with
  | .literal x _, .literal y _ => some (none, x, y)
  | .literal x _, v => (v.int?).bind fun (t, y) =>
    if t.inRange x then some (some t, x, y) else (literalWiden t x).map fun t' => (some t', x, y)
  | v, .literal y _ => (v.int?).bind fun (t, x) =>
    if t.inRange y then some (some t, x, y) else (literalWiden t y).map fun t' => (some t', x, y)
  | u, v => do
    let (ta, x) ← u.int?
    let (tb, y) ← v.int?
    let t ← commonIntType ta tb
    pure (some t, x, y)

def intResult (t : Option IntTy) (i : Int) : Value :=
  match t with
  | some t => mkInt t i
  | none => .literal i

def literalBase (i : Int) : IntTy :=
  if i < 0 then .sint ⟨256, by decide⟩ else uint256Ty

/-- Shift amount / exponent: an unsigned integer or a non-negative literal. -/
def natOperand : Value → Option Nat
  | .uint _ n => some n
  | .literal i _ => if i ≥ 0 then some i.toNat else none
  | _ => none

def bytesZip (f : UInt8 → UInt8 → UInt8) : Value → Value → Option Value
  | .fixedBytes n a, .fixedBytes m b =>
    if n = m ∧ a.length = b.length then some (.fixedBytes n (List.zipWith f a b)) else none
  | _, _ => none

def cmpNat (op : BinOp) (x y : Nat) : Option Value :=
  match op with
  | .lt => some (.bool (decide (x < y)))
  | .le => some (.bool (decide (x ≤ y)))
  | .gt => some (.bool (decide (x > y)))
  | .ge => some (.bool (decide (x ≥ y)))
  | .eq => some (.bool (decide (x = y)))
  | .ne => some (.bool (decide (x ≠ y)))
  | _ => none

def cmpInt (op : BinOp) (x y : Int) : Option Value :=
  match op with
  | .lt => some (.bool (decide (x < y)))
  | .le => some (.bool (decide (x ≤ y)))
  | .gt => some (.bool (decide (x > y)))
  | .ge => some (.bool (decide (x ≥ y)))
  | .eq => some (.bool (decide (x = y)))
  | .ne => some (.bool (decide (x ≠ y)))
  | _ => none

def isCmp : BinOp → Bool
  | .lt | .le | .gt | .ge | .eq | .ne => true
  | _ => false

def bytesNat : Value → Option Nat
  | .fixedBytes _ bs => some (bytesToNatBE bs)
  | _ => none

def addrNat : Value → Option Nat
  | .address a => some a.toNat
  | .contract _ a => some a.toNat
  | _ => none

/-- Bytes of a number literal converted to `bytesN` (`n + 1` bytes): zero always, otherwise only a
    hex literal with exactly `2 * (n + 1)` digits (solc 0.8; decimal literals never convert). -/
def literalBytes? (i : Int) (hexDigits : Option Nat) (n : Fin 32) : Option (List UInt8) :=
  if i = 0 then some (List.replicate (n.val + 1) 0)
  else if hexDigits = some (2 * (n.val + 1)) ∧ 0 ≤ i then some (natToBytesBE i.toNat (n.val + 1))
  else none

/-- A number literal meeting `bytesN` in a binary operator takes that type (same rule). -/
def adoptBytes : Value → Value → Value × Value
  | .fixedBytes n bs, .literal i hd => (.fixedBytes n bs, (literalBytes? i hd n).elim (.literal i hd) (.fixedBytes n ·))
  | .literal i hd, .fixedBytes n bs => ((literalBytes? i hd n).elim (.literal i hd) (.fixedBytes n ·), .fixedBytes n bs)
  | a, b => (a, b)

/-- Binary operators other than `&&`/`||` (short-circuited by the rules). -/
def binop (checked : Bool) (op : BinOp) (a b : Value) : Op Value := do
  -- booleans
  if let (some x, some y) := (toBool a, toBool b) then
    match op with
    | .eq => return .bool (x == y)
    | .ne => return .bool (x != y)
    | .and => return .bool (x && y)
    | .or => return .bool (x || y)
    | _ => Op.stuck
  -- addresses and contracts
  if let (some x, some y) := (addrNat a, addrNat b) then
    return ← Op.ofOpt (cmpNat op x y)
  -- fixed bytes (a number literal operand converts by the `bytesN` literal rule)
  let (a, b) := adoptBytes a b
  if let (.fixedBytes _ _, .fixedBytes _ _) := (a, b) then
    match op with
    | .bitAnd => return ← Op.ofOpt (bytesZip (· &&& ·) a b)
    | .bitOr => return ← Op.ofOpt (bytesZip (· ||| ·) a b)
    | .bitXor => return ← Op.ofOpt (bytesZip (· ^^^ ·) a b)
    | _ =>
      if isCmp op then
        if let (some x, some y) := (bytesNat a, bytesNat b) then return ← Op.ofOpt (cmpNat op x y)
        else Op.stuck
      else Op.stuck
  -- fixed bytes shifts
  if let (.fixedBytes n bs, _) := (a, b) then
    let some s := natOperand b | Op.stuck
    let width := 8 * (n.val + 1)
    let x := bytesToNatBE bs
    match op with
    | .shl => return .fixedBytes n (natToBytesBE (if s ≥ width then 0 else x * 2 ^ s) (n.val + 1))
    | .shr => return .fixedBytes n (natToBytesBE (if s ≥ width then 0 else x / 2 ^ s) (n.val + 1))
    | _ => Op.stuck
  -- enums
  if let (.enum q e x, .enum q' f y) := (a, b) then
    if e == f && q == q' then return ← Op.ofOpt (cmpNat op x y) else Op.stuck
  -- shifts and exponentiation take the left operand's type
  match op with
  | .shl | .shr | .exp =>
    let some s := natOperand b | Op.stuck
    let (t, x) ← match a with
      | .literal x _ => pure (literalBase x, x)
      | v => Op.ofOpt v.int?
    match op with
    | .shl => return mkInt t (shl t x s)
    | .shr => return mkInt t (shr t x s)
    | _ =>
      match a, b with
      | .literal x _, .literal _ _ => return .literal (x ^ s)   -- exact (constant expression)
      | _, _ =>
        match exp t checked x s with
        | .ok r => return mkInt t r
        | .error p => Op.panic p
  | _ =>
    let some (t, x, y) := unifyInts a b | Op.stuck
    if isCmp op then return ← Op.ofOpt (cmpInt op x y)
    match t with
    | none =>
      -- literal–literal: exact
      match op with
      | .add => return .literal (x + y)
      | .sub => return .literal (x - y)
      | .mul => return .literal (x * y)
      | .div => if y = 0 ∨ x % y ≠ 0 then Op.stuck else return .literal (Int.tdiv x y)   -- rational results are not modelled
      | .mod => if y = 0 then Op.stuck else return .literal (Int.tmod x y)
      | .bitAnd => if x ≥ 0 ∧ y ≥ 0 then return .literal (x.toNat &&& y.toNat) else Op.stuck
      | .bitOr => if x ≥ 0 ∧ y ≥ 0 then return .literal (x.toNat ||| y.toNat) else Op.stuck
      | .bitXor => if x ≥ 0 ∧ y ≥ 0 then return .literal (x.toNat ^^^ y.toNat) else Op.stuck
      | _ => Op.stuck
    | some t =>
      let lift (r : Except Panic Int) : Op Value :=
        match r with
        | .ok v => pure (mkInt t v)
        | .error p => Op.panic p
      match op with
      | .add => lift (add t checked x y)
      | .sub => lift (sub t checked x y)
      | .mul => lift (mul t checked x y)
      | .div => lift (div t checked x y)
      | .mod => lift (mod t x y)
      | .bitAnd => return mkInt t (bitAnd t x y)
      | .bitOr => return mkInt t (bitOr t x y)
      | .bitXor => return mkInt t (bitXor t x y)
      | _ => Op.stuck

def unop (checked : Bool) (op : UnOp) (v : Value) : Op Value := do
  match op, v with
  | .not, .bool b => return .bool (!b)
  | .neg, .literal i _ => return .literal (-i)
  | .neg, .sint w i =>
    match neg (.sint w) checked i with
    | .ok r => return .sint w r
    | .error p => Op.panic p
  | .bitNot, .fixedBytes n bs => return .fixedBytes n (bs.map (~~~ ·))
  | .bitNot, v =>
    let some (t, x) := v.int? | Op.stuck
    return mkInt t (bitNot t x)
  | _, _ => Op.stuck

/-! ## Conversions -/

/-- Implicit conversion to `ty` (value types; references are handled by assignment rules). -/
def implicitConv (env : TypeEnv) (h : Heap) (v : Value) (ty : Ty) : Option (Value × Heap) :=
  match v, ty with
  | .literal i _, .uint w => if IntTy.inRange (.uint w) i then some (.uint w i.toNat, h) else none
  | .literal i _, .int w => if IntTy.inRange (.sint w) i then some (.sint w i, h) else none
  | .uint w n, .uint w' => if w.val ≤ w'.val then some (.uint w' n, h) else none
  | .sint w i, .int w' => if w.val ≤ w'.val then some (.sint w' i, h) else none
  | .bool b, .bool => some (.bool b, h)
  | .address a, .address _ => some (.address a, h)
  -- an address literal: a hex literal with exactly 40 digits (the checksum is not modelled)
  | .literal i hd, .address _ =>
    if hd = some 40 ∧ 0 ≤ i ∧ i < 2 ^ 160 then some (.address (EVM.address i.toNat), h) else none
  | .contract c a, .user _ n => if c == n then some (.contract c a, h) else none
  | .enum q e i, .user q' n => if e == n && q == q' then some (.enum q e i, h) else none
  -- a value type converts to itself only
  | .wrapped q t u, .user q' n => if t == n && q == q' then some (.wrapped q t u, h) else none
  | .fixedBytes n bs, .fixedBytes n' =>
    if n.val ≤ n'.val then some (.fixedBytes n' (bs ++ List.replicate (n'.val - n.val) 0), h) else none
  -- number literal to `bytesN`: zero, or a hex literal with exactly `2N` digits (solc 0.8)
  | .literal i hd, .fixedBytes n => (literalBytes? i hd n).map fun bs => (.fixedBytes n bs, h)
  | .strLit s, .fixedBytes n =>
    if s.size ≤ n.val + 1 then some (.fixedBytes n (s.toList ++ List.replicate (n.val + 1 - s.size) 0), h) else none
  | .strLit s, .bytes => let (h', id) := h.alloc (.bytes false s); some (.memRef id, h')
  | .strLit s, .string => let (h', id) := h.alloc (.bytes true s); some (.memRef id, h')
  | .memRef id, _ => some (.memRef id, h)
  | .storageRef er t, _ => some (.storageRef er t, h)
  | .raw t w, _ => if t == ty then some (.raw t w, h) else none
  | _, _ => none

/-- Explicit conversion `T(v)` (0.8 rules; `none` = not allowed). -/
def explicitConv (env : TypeEnv) (h : Heap) (v : Value) (ty : Ty) : Op (Value × Heap) := do
  -- `bytesN(b)` on a byte array: the first `N` bytes, zero-padded on the right when shorter
  -- (`bytes(s)` of a memory string is the same object, so the string flag is not looked at)
  if let (.memRef id, .fixedBytes k) := (v, ty) then
    match h.get? id with
    | some (.bytes _ d) =>
      let bs := d.toList.take (k.val + 1)
      return (.fixedBytes k (bs ++ List.replicate (k.val + 1 - bs.length) 0), h)
    | _ => Op.stuck
  -- `bytes(s)` / `string(b)` on a storage value: the same location under the other type
  if let (.storageRef er sty, tty) := (v, ty) then
    if (sty == .string && tty == .bytes) || (sty == .bytes && tty == .string) then return (.storageRef er tty, h)
  if let some r := implicitConv env h v ty then return r
  match v, ty with
  -- integer width / sign changes (one attribute at a time)
  | .uint w n, .uint w' => return (.uint w' (n % 2 ^ w'.val), h)
  | .sint w i, .int w' => return (.sint w' (IntTy.wrap (.sint w') i), h)
  | .uint w n, .int w' => if w.val = w'.val then return (.sint w' (IntTy.wrap (.sint w') n), h) else Op.stuck
  | .sint w i, .uint w' => if w.val = w'.val then return (.uint w' (IntTy.toWord (.uint w') i), h) else Op.stuck
  | .literal i _, .address _ => if 0 ≤ i ∧ i < 2 ^ 160 then return (.address (EVM.address i.toNat), h) else Op.stuck
  | .literal i _, .user q n =>
    match env.enum? q n with
    | some e => if 0 ≤ i ∧ i < e.members.length then return (.enum q n i.toNat, h) else Op.stuck
    | none => Op.stuck
  | .uint w n, .address _ => if w.val = 160 then return (.address (EVM.address n), h) else Op.stuck
  | .address a, .uint w => if w.val = 160 then return (.uint w a.toNat, h) else Op.stuck
  -- `address` and `bytes20`
  | .address a, .fixedBytes k => if k.val = 19 then return (.fixedBytes k (natToBytesBE a.toNat 20), h) else Op.stuck
  | .fixedBytes k bs, .address _ => if k.val = 19 then return (.address (EVM.address (bytesToNatBE bs)), h) else Op.stuck
  | .address a, .address _ => return (.address a, h)
  | .address a, .user q n =>
    if (env.contractKind? n).isSome && (env.enum? q n).isNone then return (.contract n a, h) else Op.stuck
  | .contract _ a, .address _ => return (.address a, h)
  | .contract _ a, .user q n =>
    if (env.contractKind? n).isSome && (env.enum? q n).isNone then return (.contract n a, h) else Op.stuck
  | .uint w n, .fixedBytes k => if w.val = 8 * (k.val + 1) then return (.fixedBytes k (natToBytesBE n (k.val + 1)), h) else Op.stuck
  | .sint w i, .fixedBytes k =>
    if w.val = 8 * (k.val + 1) then return (.fixedBytes k (natToBytesBE (IntTy.toWord (.sint w) i) (k.val + 1)), h) else Op.stuck
  | .fixedBytes k bs, .uint w => if w.val = 8 * (k.val + 1) then return (.uint w (bytesToNatBE bs), h) else Op.stuck
  | .fixedBytes k bs, .fixedBytes k' =>
    if k'.val < k.val then return (.fixedBytes k' (bs.take (k'.val + 1)), h)
    else return (.fixedBytes k' (bs ++ List.replicate (k'.val - k.val) 0), h)
  | .uint _ n, .user q e =>
    match env.enum? q e with
    | some en => if n < en.members.length then return (.enum q e n, h) else Op.panic .enumRange
    | none => Op.stuck
  | .sint _ i, .user q e =>
    match env.enum? q e with
    | some en => if 0 ≤ i ∧ i < en.members.length then return (.enum q e i.toNat, h) else Op.panic .enumRange
    | none => Op.stuck
  | .enum _ _ i, .uint w => if i < 2 ^ w.val then return (.uint w i, h) else Op.stuck
  | .memRef id, .bytes =>
    match h.get? id with
    | some (.bytes _ d) => let (h', id') := h.alloc (.bytes false d); return (.memRef id', h')
    | _ => Op.stuck
  | .memRef id, .string =>
    match h.get? id with
    | some (.bytes _ d) => let (h', id') := h.alloc (.bytes true d); return (.memRef id', h')
    | _ => Op.stuck
  | _, _ => Op.stuck

/-- `T.wrap(v)` for the value type `t`: `v` converted to the underlying type and tagged. -/
def wrapValue (env : TypeEnv) (h : Heap) (t : ValueTypeInfo) (v : Value) : Option Value :=
  match implicitConv env h v t.underlying with
  | some (u, _) => if u.isElem then some (.wrapped t.qual t.name u) else none
  | none => none

/-- `T.unwrap(v)` for the value type `t`: the value `wrap` tagged. -/
def unwrapValue (t : ValueTypeInfo) : Value → Option Value
  | .wrapped q n u => if n == t.name && q == t.qual then some u else none
  | _ => none

/-! ## Storage scalars and lengths -/

def storageTyOf : Ty → Option Solm.StorageType
  | .bytes => some .bytes
  | .string => some .string
  | _ => none

def readScalar (cfg : Config) (env : TypeEnv) (evm : EVM.State) (er : Solm.EvaledStorageRef) (ty : Ty) :
    Option Value := do
  let loc ← cfg.storage.layout er evm
  scalarOfAbi env ty (Storage.storageLocLoad evm loc)

def writeScalar (cfg : Config) (evm : EVM.State) (er : Solm.EvaledStorageRef) (v : Value) :
    Option EVM.State := do
  let loc ← cfg.storage.layout er evm
  let sv ← scalarToAbi v
  Storage.storageLocStore evm loc sv

def liftRead {α} : Option (Storage.StorageReadResult α) → Op α
  | some (.ok a) => pure a
  | some .revert => Op.panic .storageBytes
  | _ => Op.stuck

def readBytesStorage (cfg : Config) (evm : EVM.State) (er : Solm.EvaledStorageRef) (st : Solm.StorageType) :
    Op ByteArray := do
  match ← liftRead (cfg.storage.readValue? er st evm) with
  | .bytes b => pure b
  | _ => Op.stuck

def writeBytesStorage (cfg : Config) (evm : EVM.State) (er : Solm.EvaledStorageRef)
    (st : Solm.StorageType) (data : ByteArray) : Op EVM.State :=
  liftRead (cfg.storage.writeValue? er st (.bytes data) evm)

def clearBytesStorage (cfg : Config) (evm : EVM.State) (er : Solm.EvaledStorageRef)
    (st : Solm.StorageType) : Op EVM.State :=
  liftRead (cfg.storage.clearValue? er st evm)

/-- The bytes of a `bytes` / `string` argument of `keccak256`, `sha256`, `ripemd160` or `concat`: a
    literal, a memory object, or a storage value (solc copies it to memory). -/
def bytesOf (cfg : Config) (m : Machine) : Value → Op ByteArray
  | .strLit s => pure s
  | .memRef id => match m.heap.get? id with | some (.bytes _ d) => pure d | _ => Op.stuck
  | .storageRef er ty => match storageTyOf ty with | some st => readBytesStorage cfg m.evm er st | none => Op.stuck
  | _ => Op.stuck

/-- `bytesN(d)`: the first `N` bytes, zero-padded on the right when shorter. -/
def fixedOfBytes (k : Fin 32) (d : ByteArray) : List UInt8 :=
  let bs := d.toList.take (k.val + 1)
  bs ++ List.replicate (k.val + 1 - bs.length) 0

/-- `bytesN(b)` with `b` in storage: the location, its type and `N - 1`. -/
def storageBytesConv? (v : Value) (ty : Ty) : Option (Solm.EvaledStorageRef × Ty × Fin 32) :=
  match v, ty with
  | .storageRef er sty, .fixedBytes k => some (er, sty, k)
  | _, _ => none

/-- The parts of `bytes.concat` / `string.concat`: byte arrays and `bytesN` values. -/
def concatParts (cfg : Config) (m : Machine) (vs : List Value) : Op (List ByteArray) :=
  vs.mapM fun
    | .fixedBytes _ bs => pure ⟨bs.toArray⟩
    | v => bytesOf cfg m v

def lengthRef (er : Solm.EvaledStorageRef) : Solm.EvaledStorageRef :=
  { er with steps := er.steps ++ [.length] }

def elemRef (er : Solm.EvaledStorageRef) (i : Nat) : Solm.EvaledStorageRef :=
  { er with steps := er.steps ++ [.aindex (.int i)] }

def fieldRef (er : Solm.EvaledStorageRef) (f : Ident) : Solm.EvaledStorageRef :=
  { er with steps := er.steps ++ [.field f] }

def keyRef (er : Solm.EvaledStorageRef) (k : Solm.KeyValue) : Solm.EvaledStorageRef :=
  { er with steps := er.steps ++ [.mindex k] }

def dynArrayLength (cfg : Config) (evm : EVM.State) (er : Solm.EvaledStorageRef) : Option Nat := do
  let loc ← cfg.storage.layout (lengthRef er) evm
  match Storage.storageLocLoad evm loc with
  | .int i => some i.toNat
  | _ => none

def writeDynArrayLength (cfg : Config) (evm : EVM.State) (er : Solm.EvaledStorageRef) (n : Nat) :
    Option EVM.State := do
  let loc ← cfg.storage.layout (lengthRef er) evm
  Storage.storageLocStore evm loc (.int n)

/-- Length of a storage array / `bytes` / `string`. -/
def storageLength (cfg : Config) (evm : EVM.State) (er : Solm.EvaledStorageRef) (ty : Ty) : Op Nat :=
  match ty with
  | .dynArray _ => Op.ofOpt (dynArrayLength cfg evm er)
  | .array _ n => pure n
  | .bytes | .string => liftRead (cfg.storage.readBytesLength er evm)
  | _ => Op.stuck

/-! ## Deep storage access -/

/-- Read a storage value of type `ty` (reference types are copied into fresh memory objects). -/
def readStorageDeep (cfg : Config) (env : TypeEnv) : Nat → EVM.State → Heap → Solm.EvaledStorageRef → Ty →
    Op (Value × Heap)
  | 0, _, _, _, _ => Op.stuck
  | fuel + 1, evm, h, er, ty =>
    match storageTyOf ty with
    | some st => do
      let data ← readBytesStorage cfg evm er st
      let (h', id) := h.alloc (.bytes (ty == .string) data)
      pure (.memRef id, h')
    | none =>
      if isValueType env ty then
        Op.ofOpt ((readScalar cfg env evm er ty).map (·, h))
      else match ty with
        | .dynArray e => do
          let n ← Op.ofOpt (dynArrayLength cfg evm er)
          readArray fuel evm h er e n false
        | .array e n => readArray fuel evm h er e n true
        | .user q n => do
          let some s := env.struct? q n | Op.stuck
          let (fields, h') ← s.fields.foldlM (fun (acc, h) (fty, fname) => do
            match fty with
            | .mapping .. => pure (acc, h)
            | _ =>
              let (v, h') ← readStorageDeep cfg env fuel evm h (fieldRef er fname) fty
              pure (acc ++ [(fname, v)], h')) (([] : List (Ident × Value)), h)
          let (h'', id) := h'.alloc (.struct ty fields)
          pure (.memRef id, h'')
        | _ => Op.stuck
where
  readArray (fuel : Nat) (evm : EVM.State) (h : Heap) (er : Solm.EvaledStorageRef) (e : Ty) (n : Nat)
      (fixed : Bool) : Op (Value × Heap) := do
    let (elems, h') ← (List.range n).foldlM (fun (acc, h) i => do
      let (v, h') ← readStorageDeep cfg env fuel evm h (elemRef er i) e
      pure (acc ++ [v], h')) (([] : List Value), h)
    let (h'', id) := h'.alloc (.array e elems fixed)
    pure (.memRef id, h'')

/-- `delete` / zeroing of a storage value of type `ty` (mappings are skipped). -/
def clearStorage (cfg : Config) (env : TypeEnv) : Nat → EVM.State → Solm.EvaledStorageRef → Ty → Op EVM.State
  | 0, _, _, _ => Op.stuck
  | fuel + 1, evm, er, ty =>
    match storageTyOf ty with
    | some st => clearBytesStorage cfg evm er st
    | none =>
      match zeroValue env ty with
      | some z => Op.ofOpt (writeScalar cfg evm er z)
      | none =>
        match ty with
        | .mapping .. => pure evm
        | .dynArray e => do
          let n ← Op.ofOpt (dynArrayLength cfg evm er)
          let evm' ← clearRange fuel evm er e 0 n
          Op.ofOpt (writeDynArrayLength cfg evm' er 0)
        | .array e n => clearRange fuel evm er e 0 n
        | .user q n => do
          let some s := env.struct? q n | Op.stuck
          s.fields.foldlM (fun evm (fty, fname) => clearStorage cfg env fuel evm (fieldRef er fname) fty) evm
        | _ => Op.stuck
where
  clearRange (fuel : Nat) (evm : EVM.State) (er : Solm.EvaledStorageRef) (e : Ty) (lo hi : Nat) :
      Op EVM.State :=
    (List.range (hi - lo)).foldlM (fun evm k => clearStorage cfg env fuel evm (elemRef er (lo + k)) e) evm

/-- Write a (memory or scalar) value of type `ty` into storage. -/
def writeStorageDeep (cfg : Config) (env : TypeEnv) : Nat → EVM.State → Heap → Solm.EvaledStorageRef → Ty →
    Value → Op EVM.State
  | 0, _, _, _, _, _ => Op.stuck
  | fuel + 1, evm, h, er, ty, v =>
    match v with
    | .storageRef er' ty' => do
      -- storage → storage copy
      let (mv, h') ← readStorageDeep cfg env fuel evm h er' ty'
      writeStorageDeep cfg env fuel evm h' er ty mv
    | .memRef id =>
      match ty, h.get? id with
      | .bytes, some (.bytes _ d) => writeBytesStorage cfg evm er .bytes d
      | .string, some (.bytes _ d) => writeBytesStorage cfg evm er .string d
      | .dynArray e, some (.array _ elems _) => do
        let old ← Op.ofOpt (dynArrayLength cfg evm er)
        let evm₁ ← Op.ofOpt (writeDynArrayLength cfg evm er elems.length)
        let evm₂ ← writeElems fuel evm₁ h er e elems
        -- shrink: clear the removed tail
        (List.range (old - elems.length)).foldlM
          (fun evm k => clearStorage cfg env fuel evm (elemRef er (elems.length + k)) e) evm₂
      | .array e n, some (.array _ elems _) =>
        if elems.length = n then writeElems fuel evm h er e elems else Op.stuck
      | .user q n, some (.struct _ fields) => do
        let some s := env.struct? q n | Op.stuck
        s.fields.foldlM (fun evm (fty, fname) =>
          match fty with
          | .mapping .. => pure evm
          | _ =>
            match fields.find? (·.1 == fname) with
            | some (_, fv) => writeStorageDeep cfg env fuel evm h (fieldRef er fname) fty fv
            | none => Op.stuck) evm
      | _, _ => Op.stuck
    | .strLit s =>
      match storageTyOf ty with
      | some st => writeBytesStorage cfg evm er st s
      | none =>
        match implicitConv env h v ty with
        | some (v', _) => Op.ofOpt (writeScalar cfg evm er v')
        | none => Op.stuck
    -- an element of a calldata array copied to storage: validated (solc reverts with empty data)
    | .raw rty w =>
      match validateRaw env rty w with
      | .ok v' =>
        match implicitConv env h v' ty with
        | some (v'', _) => Op.ofOpt (writeScalar cfg evm er v'')
        | none => Op.stuck
      | .error _ => Op.panic .badCalldataWord
    | v =>
      match implicitConv env h v ty with
      | some (v', _) => Op.ofOpt (writeScalar cfg evm er v')
      | none => Op.stuck
where
  writeElems (fuel : Nat) (evm : EVM.State) (h : Heap) (er : Solm.EvaledStorageRef) (e : Ty)
      (elems : List Value) : Op EVM.State :=
    (elems.zipIdx).foldlM (fun evm (v, i) => writeStorageDeep cfg env fuel evm h (elemRef er i) e v) evm

/-! ## Indexing and members -/

/-- Storage element of `er : ty` at index/key `idx`: bounds-checked (`Panic 0x32`). -/
def storageIndex (cfg : Config) (env : TypeEnv) (evm : EVM.State) (h : Heap) (er : Solm.EvaledStorageRef)
    (ty : Ty) (idx : Value) : Op (Solm.EvaledStorageRef × Ty) := do
  match ty with
  | .mapping k v =>
    let some (idx', _) := implicitConv env h idx k | Op.stuck
    let some key := keyOf idx' | Op.stuck
    pure (keyRef er key, v)
  | .dynArray e =>
    let some i := natOperand idx | Op.stuck
    let n ← Op.ofOpt (dynArrayLength cfg evm er)
    if i < n then pure (elemRef er i, e) else Op.panic .outOfBounds
  | .array e n =>
    let some i := natOperand idx | Op.stuck
    if i < n then pure (elemRef er i, e) else Op.panic .outOfBounds
  | .bytes | .string =>
    let some i := natOperand idx | Op.stuck
    let n ← storageLength cfg evm er ty
    if i < n then pure (elemRef er i, .fixedBytes ⟨0, by decide⟩) else Op.panic .outOfBounds
  | _ => Op.stuck

def storageField (env : TypeEnv) (er : Solm.EvaledStorageRef) (ty : Ty) (f : Ident) :
    Option (Solm.EvaledStorageRef × Ty) := do
  let .user q n := ty | none
  let s ← env.struct? q n
  let (fty, _) ← s.fields.find? (·.2 == f)
  pure (fieldRef er f, fty)

/-- Read `obj[i]` in memory (arrays and `bytes`). -/
def memIndex (h : Heap) (obj : Nat) (idx : Value) : Op Value := do
  let some i := natOperand idx | Op.stuck
  match h.get? obj with
  | some (.array _ elems _) =>
    match elems[i]? with
    | some v => pure v
    | none => Op.panic .outOfBounds
  | some (.bytes _ d) =>
    if i < d.size then pure (.fixedBytes ⟨0, by decide⟩ [d.get! i]) else Op.panic .outOfBounds
  | _ => Op.stuck

def memField (h : Heap) (obj : Nat) (f : Ident) : Option Value := do
  match h.get? obj with
  | some (.struct _ fields) => (fields.find? (·.1 == f)).map (·.2)
  | _ => none

def memLength (h : Heap) (obj : Nat) : Option Nat :=
  match h.get? obj with
  | some (.array _ elems _) => some elems.length
  | some (.bytes _ d) => some d.size
  | _ => none

/-- `b[i]` on a `bytesN` value: one byte, `Panic(0x32)` out of range. -/
def fixedBytesIndex (bs : List UInt8) (idx : Value) : Op Value := do
  let some i := natOperand idx | Op.stuck
  match bs[i]? with
  | some b => pure (.fixedBytes ⟨0, by decide⟩ [b])
  | none => Op.panic .outOfBounds

/-- `x[lo:hi]` on a byte array or array: a fresh object holding the sub-range (`lo` defaults to 0,
    `hi` to the length).  Bad bounds revert with empty data (solc: `lo > hi` or `hi > length`). -/
def sliceObj (h : Heap) (obj : Nat) (lo hi : Option Nat) : Option (Except ByteArray (Value × Heap)) :=
  match h.get? obj with
  | some (.bytes s d) =>
    let a := lo.getD 0
    let b := hi.getD d.size
    if a ≤ b ∧ b ≤ d.size then
      let (h', id) := h.alloc (.bytes s (d.extract a b))
      some (.ok (.memRef id, h'))
    else some (.error ByteArray.empty)
  | some (.array e elems _) =>
    let a := lo.getD 0
    let b := hi.getD elems.length
    if a ≤ b ∧ b ≤ elems.length then
      let (h', id) := h.alloc (.array e ((elems.drop a).take (b - a)) false)
      some (.ok (.memRef id, h'))
    else some (.error ByteArray.empty)
  | _ => none

/-- Element / field type of a memory object. -/
def memElemTy (h : Heap) (obj : Nat) : Option Ty :=
  match h.get? obj with
  | some (.array e _ _) => some e
  | some (.bytes _ _) => some (.fixedBytes ⟨0, by decide⟩)
  | _ => none

def memFieldTy (env : TypeEnv) (h : Heap) (obj : Nat) (f : Ident) : Option Ty := do
  let some (.struct (.user q n) _) := h.get? obj | none
  let s ← env.struct? q n
  (s.fields.find? (·.2 == f)).map (·.1)

def setMemIndex (h : Heap) (obj : Nat) (i : Nat) (v : Value) : Option Heap :=
  match h.get? obj with
  | some (.array e elems fx) => if i < elems.length then some (h.set obj (.array e (elems.set i v) fx)) else none
  | some (.bytes s d) =>
    match v with
    | .fixedBytes _ [b] => if i < d.size then some (h.set obj (.bytes s (d.set! i b))) else none
    | _ => none
  | _ => none

def setMemField (h : Heap) (obj : Nat) (f : Ident) (v : Value) : Option Heap :=
  match h.get? obj with
  | some (.struct ty fields) =>
    if fields.any (·.1 == f) then
      some (h.set obj (.struct ty (fields.map fun (n, w) => if n == f then (n, v) else (n, w))))
    else none
  | _ => none

/-! ## Calldata objects -/

/-- Whether a value holds a raw calldata word (a calldata array or struct parameter, or an object
    inside one). -/
def hasRaw (h : Heap) : Nat → Value → Bool
  | 0, _ => false
  | fuel + 1, v =>
    match v with
    | .raw .. => true
    | .memRef id =>
      match h.get? id with
      | some (.array _ elems _) => elems.any (hasRaw h fuel)
      | some (.struct _ fields) => fields.any fun f => hasRaw h fuel f.2
      | _ => false
    | _ => false

/-- Copy a calldata object to memory with every word validated (a struct, an array of arrays or
    structs): a word that is not canonical reverts with empty data. -/
def validateCopy (env : TypeEnv) : Nat → Heap → Value → Op (Value × Heap)
  | 0, _, _ => Op.stuck
  | fuel + 1, h, v =>
    match v with
    | .raw ty w =>
      match validateRaw env ty w with
      | .ok v' => pure (v', h)
      | .error _ => Op.panic .badCalldataWord
    | .memRef id =>
      match h.get? id with
      | some (.array e elems fx) => do
        let (elems', h') ← elems.foldlM (fun (acc, h) x => do
          let (x', h') ← validateCopy env fuel h x
          pure (acc ++ [x'], h')) (([] : List Value), h)
        let (h'', id') := h'.alloc (.array e elems' fx)
        pure (.memRef id', h'')
      | some (.struct ty fields) => do
        let (fields', h') ← fields.foldlM (fun (acc, h) (fname, x) => do
          let (x', h') ← validateCopy env fuel h x
          pure (acc ++ [(fname, x')], h')) (([] : List (Ident × Value)), h)
        let (h'', id') := h'.alloc (.struct ty fields')
        pure (.memRef id', h'')
      | some (.bytes s d) => let (h', id') := h.alloc (.bytes s d); pure (.memRef id', h')
      | none => Op.stuck
    | v => pure (v, h)

/-- The element type of an array solc copies from calldata to memory without validation: a raw
    leaf, or a static array of such. -/
def cleanElemTy (env : TypeEnv) : Ty → Bool
  | .array e _ => cleanElemTy env e
  | e => isRawLeaf env e

/-- Copy an array of raw words (through static arrays) to memory with solc's cleanup. -/
def cleanCopy (env : TypeEnv) : Nat → Heap → Value → Op (Value × Heap)
  | 0, _, _ => Op.stuck
  | fuel + 1, h, v =>
    match v with
    | .raw ty w => do
      let v' ← cleanRaw env ty w
      pure (v', h)
    | .memRef id =>
      match h.get? id with
      | some (.array e elems fx) => do
        let (elems', h') ← elems.foldlM (fun (acc, h) x => do
          let (x', h') ← cleanCopy env fuel h x
          pure (acc ++ [x'], h')) (([] : List Value), h)
        let (h'', id') := h'.alloc (.array e elems' fx)
        pure (.memRef id', h'')
      | _ => Op.stuck
    | v => pure (v, h)

/-- Copy a calldata object to memory (`T[] memory m = xs;`, a memory parameter of an internal call,
    a struct field): an array of raw words (or of static arrays of them) is copied with solc's
    cleanup, anything else (a struct, an array of dynamic arrays or of structs) with every word
    validated. -/
def copyCalldata (env : TypeEnv) (fuel : Nat) (h : Heap) (v : Value) : Op (Value × Heap) :=
  match v with
  | .memRef id =>
    match h.get? id with
    | some (.array e _ _) => if cleanElemTy env e then cleanCopy env fuel h v else validateCopy env fuel h v
    | _ => validateCopy env fuel h v
  | v => validateCopy env fuel h v

/-- Validate every raw word of a value in place (its ABI encoding: `abi.encode`, the arguments of
    an external call, an event or an error): solc's encoder reverts with empty data on a word that
    is not canonical. -/
def validateDeep (env : TypeEnv) : Nat → Heap → Value → Op Heap
  | 0, _, _ => Op.stuck
  | fuel + 1, h, v =>
    match v with
    | .raw ty w => match validateRaw env ty w with | .ok _ => pure h | .error _ => Op.panic .badCalldataWord
    | .memRef id =>
      if hasRaw h (fuel + 1) (.memRef id) = false then pure h
      else match h.get? id with
      | some (.array e elems fx) =>
        if elems.any isRawValue then do
          let elems' ← elems.mapM fun
            | .raw ty w => match validateRaw env ty w with | .ok v' => pure v' | .error _ => Op.panic .badCalldataWord
            | x => pure x
          pure (h.set id (.array e elems' fx))
        else elems.foldlM (validateDeep env fuel) h
      | some (.struct ty fields) =>
        if fields.any fun f => isRawValue f.2 then do
          let fields' ← fields.mapM fun
            | (fname, .raw ty w) =>
              match validateRaw env ty w with
              | .ok v' => pure (fname, v')
              | .error _ => Op.panic .badCalldataWord
            | f => pure f
          let h' := h.set id (.struct ty fields')
          fields'.foldlM (fun h f => validateDeep env fuel h f.2) h'
        else fields.foldlM (fun h f => validateDeep env fuel h f.2) h
      | _ => pure h
    | _ => pure h
where
  isRawValue : Value → Bool
    | .raw .. => true
    | _ => false

/-! ## Reading and assigning -/

/-- The value of a storage reference: scalars are loaded, reference types stay references. -/
def loadIfScalar (cfg : Config) (env : TypeEnv) (evm : EVM.State) (er : Solm.EvaledStorageRef) (ty : Ty) :
    Option Value :=
  if isValueType env ty then readScalar cfg env evm er ty else some (.storageRef er ty)

/-- Convert `v` for a slot of declared type `ty` and data location `loc` (memory copies from
    storage, references alias). -/
def coerce (cfg : Config) (env : TypeEnv) (m : Machine) (v : Value) (ty : Ty) (loc : Option DataLoc) :
    Op (Value × Machine) := do
  match v with
  | .storageRef er sty =>
    if loc == some .storage then
      if sty == ty then pure (.storageRef er sty, m) else Op.stuck
    else
      let (mv, h') ← readStorageDeep cfg env fuelDefault m.evm m.heap er ty
      pure (mv, { m with heap := h' })
  | .memRef id =>
    if loc == some .storage then Op.stuck
    else if loc == some .memory && hasRaw m.heap fuelDefault (.memRef id) then do
      -- a calldata object copied to memory
      let (v', h') ← copyCalldata env fuelDefault m.heap (.memRef id)
      pure (v', { m with heap := h' })
    else pure (.memRef id, m)
  | v =>
    match implicitConv env m.heap v ty with
    | some (v', h') => pure (v', { m with heap := h' })
    | none => Op.stuck

/-- Read an lvalue (for compound assignment, `++`, `--`). -/
def readLValue (cfg : Config) (env : TypeEnv) (fr : Frame) (m : Machine) : LValue → Op Value
  | .local x => Op.ofOpt ((fr.get? x).map (·.val))
  | .storage er ty => Op.ofOpt (loadIfScalar cfg env m.evm er ty)
  | .memField obj f => Op.ofOpt (memField m.heap obj f)
  | .memIndex obj i => memIndex m.heap obj (.literal i)

/-- The declared type of an lvalue. -/
def lvalueTy (env : TypeEnv) (fr : Frame) (m : Machine) : LValue → Option Ty
  | .local x => (fr.get? x).map (·.ty)
  | .storage _ ty => some ty
  | .memField obj f => memFieldTy env m.heap obj f
  | .memIndex obj _ => memElemTy m.heap obj

/-- The value of the expression `lhs = v`: `v` converted to the type of the left-hand side (solc
    types an assignment by its left operand).  A reference keeps its right-hand side. -/
def assignedValue (env : TypeEnv) (fr : Frame) (m : Machine) (lv : LValue) (v : Value) : Value :=
  match lvalueTy env fr m lv with
  | some ty =>
    if isValueType env ty then
      match implicitConv env m.heap v ty with
      | some (v', _) => v'
      | none => v
    else v
  | none => v

/-- Assign `v` to an lvalue. -/
def assign (cfg : Config) (env : TypeEnv) (fr : Frame) (m : Machine) (lv : LValue) (v : Value) :
    Op (Frame × Machine) := do
  match lv with
  | .local x =>
    let some l := fr.get? x | Op.stuck
    let (v', m') ← coerce cfg env m v l.ty l.loc
    pure (fr.setVal x v', m')
  | .storage er ty =>
    let evm' ← writeStorageDeep cfg env fuelDefault m.evm m.heap er ty v
    pure (fr, { m with evm := evm' })
  | .memField obj f =>
    let some fty := memFieldTy env m.heap obj f | Op.stuck
    let (v', m') ← coerce cfg env m v fty (some .memory)
    let some h' := setMemField m'.heap obj f v' | Op.stuck
    pure (fr, { m' with heap := h' })
  | .memIndex obj i =>
    let some ety := memElemTy m.heap obj | Op.stuck
    let (v', m') ← coerce cfg env m v ety (some .memory)
    let some h' := setMemIndex m'.heap obj i v' | Op.stuck
    pure (fr, { m' with heap := h' })

/-- Declare a local: `ty loc name = init;` (no initialiser ⇒ zero / empty object). -/
def declare (cfg : Config) (env : TypeEnv) (fr : Frame) (m : Machine) (ty : Ty) (loc : Option DataLoc)
    (name : Ident) (init : Option Value) : Op (Frame × Machine) := do
  -- the type is written in the scope of the running code
  let ty := env.canonTy fr.here ty
  match init with
  | some v =>
    let (v', m') ← coerce cfg env m v ty loc
    pure (fr.bind name ty loc v', m')
  | none =>
    if loc == some .storage then Op.stuck
    let some (v, h') := zeroObj env fuelDefault ty 0 m.heap | Op.stuck
    pure (fr.bind name ty loc v, { m with heap := h' })

/-- Storage array `push`. -/
def storagePush (cfg : Config) (env : TypeEnv) (m : Machine) (er : Solm.EvaledStorageRef) (e : Ty)
    (v : Option Value) : Op Machine := do
  let n ← Op.ofOpt (dynArrayLength cfg m.evm er)
  let evm₁ ← Op.ofOpt (writeDynArrayLength cfg m.evm er (n + 1))
  match v with
  | some v =>
    let evm₂ ← writeStorageDeep cfg env fuelDefault evm₁ m.heap (elemRef er n) e v
    pure { m with evm := evm₂ }
  | none => pure { m with evm := evm₁ }

/-- Storage array `pop` (`Panic 0x31` on empty). -/
def storagePop (cfg : Config) (env : TypeEnv) (m : Machine) (er : Solm.EvaledStorageRef) (e : Ty) :
    Op Machine := do
  let n ← Op.ofOpt (dynArrayLength cfg m.evm er)
  if n = 0 then Op.panic .popEmpty
  let evm₁ ← clearStorage cfg env fuelDefault m.evm (elemRef er (n - 1)) e
  let evm₂ ← Op.ofOpt (writeDynArrayLength cfg evm₁ er (n - 1))
  pure { m with evm := evm₂ }

/-- The byte pushed by `b.push(x)` on storage `bytes`: `x` as a `bytes1`. -/
def pushedByte (env : TypeEnv) (h : Heap) (v : Value) : Option UInt8 :=
  match implicitConv env h v (.fixedBytes ⟨0, by decide⟩) with
  | some (.fixedBytes _ [b], _) => some b
  | _ => none

/-- `b.push(x)` / `b.push()` on storage `bytes`. -/
def bytesPush (cfg : Config) (m : Machine) (er : Solm.EvaledStorageRef) (b : UInt8) : Op Machine := do
  let d ← readBytesStorage cfg m.evm er .bytes
  let evm' ← writeBytesStorage cfg m.evm er .bytes (d.push b)
  pure { m with evm := evm' }

/-- `b.pop()` on storage `bytes` (`Panic 0x31` on empty). -/
def bytesPop (cfg : Config) (m : Machine) (er : Solm.EvaledStorageRef) : Op Machine := do
  let d ← readBytesStorage cfg m.evm er .bytes
  if d.size = 0 then Op.panic .popEmpty
  let evm' ← writeBytesStorage cfg m.evm er .bytes (d.extract 0 (d.size - 1))
  pure { m with evm := evm' }

/-! ## ABI helpers -/

/-- ABI type of a value (for `abi.encode*` without a declared target type). -/
def abiTyOfValue (env : TypeEnv) (h : Heap) : Value → Option ABIType
  | .literal i _ => (mobileType i).map fun t => .elem (.int t)
  | .strLit _ => some .string
  | .memRef id =>
    match h.get? id with
    | some (.struct ty _) => abiTypeOf env ty
    | some (.array e elems fixed) =>
      (abiTypeOf env e).map fun t => if fixed then .array t elems.length else .dynamicArray t
    | some (.bytes s _) => some (if s then .string else .bytes)
    | none => none
  | v => (v.ty?).bind (abiTypeOf env)

/-- Convert arguments to declared parameter types and into the ABI domain.  A calldata object is
    validated word by word first (solc's encoder). -/
def abiArgs (cfg : Config) (env : TypeEnv) (m : Machine) (tys : List Ty) (vs : List Value) :
    Op (List ABIValue × Machine) := do
  if tys.length ≠ vs.length then Op.stuck
  let h ← vs.foldlM (validateDeep env fuelDefault) m.heap
  let m := { m with heap := h }
  (tys.zip vs).foldlM (fun (acc, m) (ty, v) => do
    let (v', m') ← coerce cfg env m v ty (some .memory)
    let some sv := toAbi m'.heap fuelDefault v' | Op.stuck
    pure (acc ++ [sv], m')) (([] : List ABIValue), m)

/-- Bind ABI-decoded values to parameters, allocating reference types. -/
def bindParams (env : TypeEnv) (fr : Frame) (h : Heap) (params : List Param) (vs : List ABIValue) :
    Option (Frame × Heap) := do
  if params.length ≠ vs.length then none
  (params.zip vs).foldlM (fun (fr, h) (p, sv) => do
    let name ← p.name
    let (v, h') ← ofAbi env fuelDefault p.ty sv h
    pure (fr.bind name p.ty (p.loc <|> some .memory) v, h')) (fr, h)

end Solidity
