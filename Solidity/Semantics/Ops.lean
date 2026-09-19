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
  | "block", "basefee" => some (wordNat ee.header.baseFeePerGas)
  | _, _ => none

/-! ## Keys and truth values -/

def keyOf : Value → Option Solm.KeyValue
  | .uint _ n => some (.int n)
  | .sint _ i => some (.int i)
  | .literal i => some (.int i)
  | .bool b => some (.bool b)
  | .address a => some (.address a)
  | .contract _ a => some (.address a)
  | .fixedBytes n bs => some (.fixedBytes n bs)
  | .enum _ i => some (.int i)
  | _ => none

def toBool : Value → Option Bool
  | .bool b => some b
  | _ => none

/-- Validate a raw calldata word for its type (solc validates on access, reverting with empty
    data when the word is not canonical). -/
def validateRaw (ty : Ty) (w : Nat) : Except ByteArray Value :=
  match ty with
  | .bool => if w ≤ 1 then .ok (.bool (w == 1)) else .error ByteArray.empty
  | .uint bw => if w < 2 ^ bw.val then .ok (.uint bw w) else .error ByteArray.empty
  | .address _ => if w < 2 ^ 160 then .ok (.address (EVM.address w)) else .error ByteArray.empty
  | _ => .error ByteArray.empty

/-! ## Literal adoption and operators -/

/-- A literal meeting a typed integer takes that type (must fit). -/
def adopt (t : IntTy) : Value → Option Value
  | .literal i => if t.inRange i then some (mkInt t i) else none
  | v => some v

/-- Integer operands unified to a common type (`(type, a, b)`); literal–literal stays exact. -/
def unifyInts (a b : Value) : Option (Option IntTy × Int × Int) :=
  match a, b with
  | .literal x, .literal y => some (none, x, y)
  | .literal x, v => (v.int?).bind fun (t, y) => if t.inRange x then some (some t, x, y) else none
  | v, .literal y => (v.int?).bind fun (t, x) => if t.inRange y then some (some t, x, y) else none
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
  | .literal i => if i ≥ 0 then some i.toNat else none
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
  -- fixed bytes
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
  if let (.enum e x, .enum f y) := (a, b) then
    if e == f then return ← Op.ofOpt (cmpNat op x y) else Op.stuck
  -- shifts and exponentiation take the left operand's type
  match op with
  | .shl | .shr | .exp =>
    let some s := natOperand b | Op.stuck
    let (t, x) ← match a with
      | .literal x => pure (literalBase x, x)
      | v => Op.ofOpt v.int?
    match op with
    | .shl => return mkInt t (shl t x s)
    | .shr => return mkInt t (shr t x s)
    | _ =>
      match a, b with
      | .literal x, .literal _ => return .literal (x ^ s)   -- exact (constant expression)
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
      | .div => if y = 0 then Op.stuck else return .literal (Int.tdiv x y)
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
  | .neg, .literal i => return .literal (-i)
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
  | .literal i, .uint w => if IntTy.inRange (.uint w) i then some (.uint w i.toNat, h) else none
  | .literal i, .int w => if IntTy.inRange (.sint w) i then some (.sint w i, h) else none
  | .uint w n, .uint w' => if w.val ≤ w'.val then some (.uint w' n, h) else none
  | .sint w i, .int w' => if w.val ≤ w'.val then some (.sint w' i, h) else none
  | .uint w n, .int w' => if w.val < w'.val then some (.sint w' n, h) else none
  | .bool b, .bool => some (.bool b, h)
  | .address a, .address _ => some (.address a, h)
  | .contract c a, .user _ n => if c == n then some (.contract c a, h) else none
  | .enum e i, .user _ n => if e == n then some (.enum e i, h) else none
  | .fixedBytes n bs, .fixedBytes n' =>
    if n.val ≤ n'.val then some (.fixedBytes n' (bs ++ List.replicate (n'.val - n.val) 0), h) else none
  -- a zero literal converts to any `bytesN` (non-zero hex literals need the digit count: not modelled)
  | .literal 0, .fixedBytes n => some (.fixedBytes n (List.replicate (n.val + 1) 0), h)
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
  if let some r := implicitConv env h v ty then return r
  match v, ty with
  -- integer width / sign changes (one attribute at a time)
  | .uint w n, .uint w' => return (.uint w' (n % 2 ^ w'.val), h)
  | .sint w i, .int w' => return (.sint w' (IntTy.wrap (.sint w') i), h)
  | .uint w n, .int w' => if w.val = w'.val then return (.sint w' (IntTy.wrap (.sint w') n), h) else Op.stuck
  | .sint w i, .uint w' => if w.val = w'.val then return (.uint w' (IntTy.toWord (.uint w') i), h) else Op.stuck
  | .literal i, .address _ => if 0 ≤ i ∧ i < 2 ^ 160 then return (.address (EVM.address i.toNat), h) else Op.stuck
  | .literal i, .fixedBytes n => if 0 ≤ i ∧ i < 2 ^ (8 * (n.val + 1)) then return (.fixedBytes n (natToBytesBE i.toNat (n.val + 1)), h) else Op.stuck
  | .literal i, .user q n =>
    match env.enum? q n with
    | some e => if 0 ≤ i ∧ i < e.members.length then return (.enum n i.toNat, h) else Op.stuck
    | none => Op.stuck
  | .uint w n, .address _ => if w.val = 160 then return (.address (EVM.address n), h) else Op.stuck
  | .address a, .uint w => if w.val = 160 then return (.uint w a.toNat, h) else Op.stuck
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
    | some en => if n < en.members.length then return (.enum e n, h) else Op.panic .enumRange
    | none => Op.stuck
  | .enum _ i, .uint w => if i < 2 ^ w.val then return (.uint w i, h) else Op.stuck
  | .memRef id, .bytes =>
    match h.get? id with
    | some (.bytes _ d) => let (h', id') := h.alloc (.bytes false d); return (.memRef id', h')
    | _ => Op.stuck
  | .memRef id, .string =>
    match h.get? id with
    | some (.bytes _ d) => let (h', id') := h.alloc (.bytes true d); return (.memRef id', h')
    | _ => Op.stuck
  | _, _ => Op.stuck

/-! ## Storage scalars and lengths -/

def storageTyOf : Ty → Option Solm.StorageType
  | .bytes => some .bytes
  | .string => some .string
  | _ => none

def readScalar (cfg : Config) (env : TypeEnv) (evm : EVM.State) (er : Solm.EvaledStorageRef) (ty : Ty) :
    Option Value := do
  let loc ← cfg.storage.layout er evm
  scalarOfSolm env ty (Storage.storageLocLoad evm loc)

def writeScalar (cfg : Config) (evm : EVM.State) (er : Solm.EvaledStorageRef) (v : Value) :
    Option EVM.State := do
  let loc ← cfg.storage.layout er evm
  let sv ← scalarToSolm v
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
          readArray fuel evm h er e n
        | .array e n => readArray fuel evm h er e n
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
  readArray (fuel : Nat) (evm : EVM.State) (h : Heap) (er : Solm.EvaledStorageRef) (e : Ty) (n : Nat) :
      Op (Value × Heap) := do
    let (elems, h') ← (List.range n).foldlM (fun (acc, h) i => do
      let (v, h') ← readStorageDeep cfg env fuel evm h (elemRef er i) e
      pure (acc ++ [v], h')) (([] : List Value), h)
    let (h'', id) := h'.alloc (.array e elems)
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
      | .dynArray e, some (.array _ elems) => do
        let old ← Op.ofOpt (dynArrayLength cfg evm er)
        let evm₁ ← Op.ofOpt (writeDynArrayLength cfg evm er elems.length)
        let evm₂ ← writeElems fuel evm₁ h er e elems
        -- shrink: clear the removed tail
        (List.range (old - elems.length)).foldlM
          (fun evm k => clearStorage cfg env fuel evm (elemRef er (elems.length + k)) e) evm₂
      | .array e n, some (.array _ elems) =>
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
  | some (.array _ elems) =>
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
  | some (.array _ elems) => some elems.length
  | some (.bytes _ d) => some d.size
  | _ => none

/-- Element / field type of a memory object. -/
def memElemTy (h : Heap) (obj : Nat) : Option Ty :=
  match h.get? obj with
  | some (.array e _) => some e
  | some (.bytes _ _) => some (.fixedBytes ⟨0, by decide⟩)
  | _ => none

def memFieldTy (env : TypeEnv) (h : Heap) (obj : Nat) (f : Ident) : Option Ty := do
  let some (.struct (.user q n) _) := h.get? obj | none
  let s ← env.struct? q n
  (s.fields.find? (·.2 == f)).map (·.1)

def setMemIndex (h : Heap) (obj : Nat) (i : Nat) (v : Value) : Option Heap :=
  match h.get? obj with
  | some (.array e elems) => if i < elems.length then some (h.set obj (.array e (elems.set i v))) else none
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
    if loc == some .storage then Op.stuck else pure (.memRef id, m)
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

/-! ## ABI helpers -/

/-- ABI type of a value (for `abi.encode*` without a declared target type). -/
def abiTyOfValue (env : TypeEnv) (h : Heap) : Value → Option ABIType
  | .literal i => (mobileType i).map fun t => .elem (.int t)
  | .strLit _ => some .string
  | .memRef id =>
    match h.get? id with
    | some (.struct ty _) => abiTypeOf env ty
    | some (.array e _) => (abiTypeOf env e).map .dynamicArray
    | some (.bytes s _) => some (if s then .string else .bytes)
    | none => none
  | v => (v.ty?).bind (abiTypeOf env)

/-- Convert arguments to declared parameter types and into the `Solm.Value` domain. -/
def abiArgs (cfg : Config) (env : TypeEnv) (m : Machine) (tys : List Ty) (vs : List Value) :
    Op (List Solm.Value × Machine) := do
  if tys.length ≠ vs.length then Op.stuck
  (tys.zip vs).foldlM (fun (acc, m) (ty, v) => do
    let (v', m') ← coerce cfg env m v ty (some .memory)
    let some sv := toAbi m'.heap fuelDefault v' | Op.stuck
    pure (acc ++ [sv], m')) (([] : List Solm.Value), m)

/-- Bind ABI-decoded values to parameters, allocating reference types. -/
def bindParams (env : TypeEnv) (fr : Frame) (h : Heap) (params : List Param) (vs : List Solm.Value) :
    Option (Frame × Heap) := do
  if params.length ≠ vs.length then none
  (params.zip vs).foldlM (fun (fr, h) (p, sv) => do
    let name ← p.name
    let (v, h') ← ofAbi env fuelDefault p.ty sv h
    pure (fr.bind name p.ty (p.loc <|> some .memory) v, h')) (fr, h)

end Solidity
