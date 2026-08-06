import ABI.Encode
import Solm.Value

/-! The evaluation monad (`EvalResult`) and value-level primitive operations. -/

namespace Solm

open ABI

/-- Solm evaluation errors. Should never happen in well-formed programs -/
inductive EvalError where
  | unboundVariable
  | typeError
  | storageError
  deriving DecidableEq, Repr, Inhabited

/-- Result of evaluating an Solm expression:
    - a value (`ok`)
    - a `revert`
    - or an error, which indicates an ill-formed program
-/
inductive EvalResult (α : Type) where
  | ok : α -> EvalResult α
  | revert : EvalResult α
  | error : EvalError -> EvalResult α
  deriving Repr, DecidableEq

namespace EvalResult

@[inline] def bind : EvalResult α -> (α -> EvalResult β) -> EvalResult β
  | .ok a,    f => f a
  | .revert,  _ => .revert
  | .error e, _ => .error e

instance : Monad EvalResult where
  pure := .ok
  bind := bind

/-- Lift an `Option`, mapping `none` to the model-level `error e`. -/
@[inline] def ofOption (e : EvalError) : Option α -> EvalResult α
  | some a => .ok a
  | none   => .error e

/-- Sequence a list of results, short-circuiting on the first `revert`/`error`. -/
def seqList : List (EvalResult α) -> EvalResult (List α)
  | [] => .ok []
  | x :: xs => do
      let a <- x
      let as <- seqList xs
      .ok (a :: as)

end EvalResult

def envValue (evm : EVM.State) : EnvVar -> Value
  | .caller => .address evm.executionEnv.source
  | .origin => .address evm.executionEnv.sender
  | .callvalue => .int (Int.ofNat evm.executionEnv.weiValue.val)
  | .this => .address evm.executionEnv.codeOwner
  | .timestamp => .int (Int.ofNat (Ethereum.UInt256.ofNat evm.executionEnv.header.timestamp).toNat)
  | .chainid => .int (Int.ofNat Ethereum.chainId)
  | .selfbalance =>
      .int (Int.ofNat ((evm.lookupAccount evm.executionEnv.codeOwner).option
        (EVM.Word.ofNat 0) (·.balance)).toNat)
  | .gasprice => .int (Int.ofNat (EVM.Word.ofNat evm.executionEnv.gasPrice).toNat)
  -- Each mirrors the evmlean opcode handler (Semantics.lean:485-531) / StateOps.lean.
  | .number => .int (Int.ofNat (EVM.Word.ofNat evm.executionEnv.header.number).toNat)      -- NUMBER
  | .coinbase => .address evm.executionEnv.header.beneficiary                               -- COINBASE
  | .gaslimit => .int (Int.ofNat (EVM.Word.ofNat evm.executionEnv.header.gasLimit).toNat)   -- GASLIMIT
  | .prevrandao => .int (Int.ofNat evm.executionEnv.header.prevRandao.toNat)                -- PREVRANDAO
  | .basefee => .int (Int.ofNat (EVM.Word.ofNat evm.executionEnv.header.baseFeePerGas).toNat) -- BASEFEE
  | .msgSig =>
      let b := evm.executionEnv.calldata.toList.take 4
      .fixedBytes ⟨3, by decide⟩ (b ++ List.replicate (4 - b.length) 0)
  | .msgData => .bytes evm.executionEnv.calldata

def valueToKey? (v : Value) : Option KeyValue :=
  match v with
  | .int i => pure $ .int i
  | .bool b => pure $ .bool b
  | .address a => pure $ .address a
  -- Reject a length-mismatched `bytesN` key loudly (avoid `keyValueToWord`'s silent slot-`0` fallback).
  | .fixedBytes n bs => if bs.length = n.val + 1 then pure (.fixedBytes n bs) else .none
  | _ => .none

def lookupAssoc [DecidableEq α] (entries : List (α × β)) (key : α) : Option β :=
  match entries with
  | [] => none
  | (k, v) :: rest => if k = key then some v else lookupAssoc rest key

def updateAssoc [DecidableEq α] (entries : List (α × β)) (key : α) (value : β) :
    List (α × β) :=
  match entries with
  | [] => [(key, value)]
  | (k, v) :: rest =>
      if k = key then
        (key, value) :: rest
      else
        (k, v) :: updateAssoc rest key value

def updateNth? (xs : List α) (index : Nat) (value : α) : Option (List α) :=
  match xs, index with
  | [], _ => none
  | _ :: rest, 0 => some (value :: rest)
  | x :: rest, i + 1 => do
      let rest' <- updateNth? rest i value
      pure (x :: rest')

def lookupNth? (xs : List α) (index : Nat) : Option α :=
  match xs, index with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: rest, i + 1 => lookupNth? rest i

def intToNat? (n : Int) : Option Nat :=
  if n < 0 then none else some n.toNat

def lookupField? (v : Value) (name : Ident) : Option Value :=
  match v with
  | .struct _ fields => lookupAssoc fields name
  | _ => none

def updateField? (v : Value) (name : Ident) (value : Value) : Option Value :=
  match v with
  | .struct tag fields =>
      match lookupAssoc fields name with
      | some _ => some (.struct tag (updateAssoc fields name value))
      | none => none
  | _ => none

def lookupIndex? (container key : Value) : Option Value :=
  match container with
  | .array elems =>
      match key with
      | .int i => do
          let idx <- intToNat? i
          lookupNth? elems idx
      | _ => none
  | .fixedBytes n bytes =>
      match key with
      | .int i => do
          if bytes.length = n.val + 1 then
            let idx <- intToNat? i
            let b <- lookupNth? bytes idx
            pure (.fixedBytes ⟨0, by decide⟩ [b])
          else
            none
      | _ => none
  | .bytes bytes =>
      match key with
      | .int i => do
          let idx <- intToNat? i
          let b <- lookupNth? bytes.toList idx
          pure (.fixedBytes ⟨0, by decide⟩ [b])
      | _ => none
  | _ => none

def updateIndex? (container key value : Value) : Option Value :=
  match container with
  | .array elems =>
      match key with
      | .int i => do
          let idx <- intToNat? i
          let elems' <- updateNth? elems idx value
          pure (.array elems')
      | _ => none
  | _ => none

def fixedBytesSize (n : Fin 32) : Nat :=
  n.val + 1

def fixedBytesValid (n : Fin 32) (bytes : List UInt8) : Bool :=
  bytes.length = fixedBytesSize n

def fixedBytesToNat? (n : Fin 32) (bytes : List UInt8) : Option Nat :=
  if fixedBytesValid n bytes then some (Ethereum.fromBytesBigEndian bytes) else none

def castValue? (v : Value) (ty : StorageType) : Option Value :=
  match ty, v with
  | .elem (.bool), .bool _ => some v
  | .elem (.address), .address _ => some v
  | .elem (.bytes expected), .fixedBytes actual _ =>
      if expected = actual then some v else none
  -- A negative int fails loudly (silent `n.toNat = 0` would be a wrong value); literal-`0` casts are ≥0.
  | .elem (.bytes expected), .int n =>
      if n < 0 then none
      else some (.fixedBytes expected ((EVM.Word.ofNat n.toNat).toBytesBE.drop (32 - (expected.val + 1))))
  -- `address(n)`: an integer cast to `address` (e.g. `address(0)`), truncated to the address width.
  | .elem (.address), .int n => if n < 0 then none else some (.address (.ofNat n.toNat))
  | .elem (.int (.uint bits)), .address a =>
      if a.toNat < EVM.twoPow bits.val then
        some (.int (Int.ofNat a.toNat))
      else
        none
  -- `uintN(bytesN)`: solc allows this cast only at equal width (`8·(n+1) = bits`); the bytes are
  -- read big-endian via the same `fixedBytesToNat?` the comparison/`bitAnd` cases use.
  | .elem (.int (.uint bits)), .fixedBytes n bs =>
      if 8 * (n.val + 1) = bits.val then
        match fixedBytesToNat? n bs with
        | some k => some (.int (Int.ofNat k))
        | none => none
      else none
  | .elem (.int intType), .int i => some (.int (normalizeInt intType i))
  | .contract _, .address _ => some v
  | .struct expected _, .struct actual _ =>
      if expected = actual then some v else none
  | .array _ _, .array _ => some v
  | .dynamicArray _, .array _ => some v
  | _, _ => none

mutual

/-- Whether a runtime value is already a valid value of an ABI type. This validates rather than
    converts: integer values must be in the declared range, and compound values must have the
    declared shape recursively. Struct values use their field order for ABI tuple validation. -/
def valueMatchesABIType : ABIType → Value → Bool
  | .elem .bool, .bool _ => true
  | .elem .address, .address _ => true
  | .elem (.int intType), .int value => normalizeInt intType value == value
  | .elem (.bytes expected), .fixedBytes actual bytes =>
      expected == actual && fixedBytesValid expected bytes
  | .elem .function, .array values =>
      values.length == 24 && values.all fun
        | .int value => 0 ≤ value && value < 256
        | _ => false
  | .array elemType length, .array values =>
      values.length == length && valuesMatchABIType elemType values
  | .dynamicArray elemType, .array values => valuesMatchABIType elemType values
  | .tuple types, .tuple values => valuesMatchABITypes types values
  | .tuple types, .struct _ fields => valuesMatchABITypes types (fields.map (·.2))
  | .bytes, .bytes _ | .string, .bytes _ => true
  | _, _ => false
termination_by type _ => (sizeOf type, 0, 0)

/-- Validate every value in a homogeneous ABI array. -/
def valuesMatchABIType (type : ABIType) : List Value → Bool
  | [] => true
  | value :: values => valueMatchesABIType type value && valuesMatchABIType type values
termination_by values => (sizeOf type, sizeOf values + 1, 1)

/-- Validate a heterogeneous ABI tuple. -/
def valuesMatchABITypes : List ABIType → List Value → Bool
  | [], [] => true
  | type :: types, value :: values =>
      valueMatchesABIType type value && valuesMatchABITypes types values
  | _, _ => false
termination_by types values => (sizeOf types, sizeOf values + 1, 2)

end

def valueMatchesOptionalABIType : Option ABIType → Value → Bool
  | none, _ => true
  | some type, value => valueMatchesABIType type value

#guard valueMatchesABIType (.elem (.int (.uint ⟨8, by decide⟩))) (.int 255)
#guard !valueMatchesABIType (.elem (.int (.uint ⟨8, by decide⟩))) (.int 256)
#guard valueMatchesABIType (.elem (.int (.sint ⟨8, by decide⟩))) (.int (-128))
#guard !valueMatchesABIType (.elem (.int (.sint ⟨8, by decide⟩))) (.int 128)
#guard valueMatchesABIType (.array (.elem .bool) 2) (.array [.bool true, .bool false])
#guard !valueMatchesABIType (.array (.elem .bool) 2) (.array [.bool true])

@[simp] theorem valueMatchesABIType_uint256_word (word : EVM.Word) :
    valueMatchesABIType (.elem (.int (.uint ⟨256, by decide⟩)))
      (.int (Int.ofNat word.toNat)) = true := by
  simp only [valueMatchesABIType, beq_iff_eq]
  exact normalizeInt_uint256_word word

theorem valueMatchesABIType_uint_word_of_lt
    (bits : BitWidth) (word : EVM.Word)
    (hfit : word.toNat < EVM.twoPow bits.val) :
    valueMatchesABIType (.elem (.int (.uint bits)))
      (.int (Int.ofNat word.toNat)) = true := by
  simp only [valueMatchesABIType, beq_iff_eq]
  exact normalizeInt_uint_eq_self bits (Int.ofNat word.toNat)
    (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hfit)

@[simp] theorem valueMatchesABIType_uint_word_of_width_256
    (bits : BitWidth) (word : EVM.Word) (hwidth : bits.val = 256) :
    valueMatchesABIType (.elem (.int (.uint bits)))
      (.int (Int.ofNat word.toNat)) = true := by
  apply valueMatchesABIType_uint_word_of_lt
  rw [hwidth]
  exact word.val.isLt

@[simp] theorem valueMatchesOptionalABIType_uint256_word (word : EVM.Word) :
    valueMatchesOptionalABIType
        (some (.elem (.int (.uint ⟨256, by decide⟩))))
      (.int (Int.ofNat word.toNat)) = true :=
  valueMatchesABIType_uint256_word word

theorem valueMatchesOptionalABIType_uint_word_of_lt
    (bits : BitWidth) (word : EVM.Word)
    (hfit : word.toNat < EVM.twoPow bits.val) :
    valueMatchesOptionalABIType (some (.elem (.int (.uint bits))))
      (.int (Int.ofNat word.toNat)) = true :=
  valueMatchesABIType_uint_word_of_lt bits word hfit

@[simp] theorem valueMatchesOptionalABIType_uint_word_of_width_256
    (bits : BitWidth) (word : EVM.Word) (hwidth : bits.val = 256) :
    valueMatchesOptionalABIType (some (.elem (.int (.uint bits))))
      (.int (Int.ofNat word.toNat)) = true :=
  valueMatchesABIType_uint_word_of_width_256 bits word hwidth

theorem valueMatchesABIType_uint_of_bounds (bits : BitWidth) (value : Int)
    (hnonneg : 0 ≤ value) (hfit : value < Int.ofNat (EVM.twoPow bits.val)) :
    valueMatchesABIType (.elem (.int (.uint bits))) (.int value) = true := by
  simp only [valueMatchesABIType, beq_iff_eq]
  exact normalizeInt_uint_eq_self bits value hnonneg hfit

theorem valueMatchesOptionalABIType_uint_of_bounds (bits : BitWidth) (value : Int)
    (hnonneg : 0 ≤ value) (hfit : value < Int.ofNat (EVM.twoPow bits.val)) :
    valueMatchesOptionalABIType (some (.elem (.int (.uint bits)))) (.int value) = true := by
  exact valueMatchesABIType_uint_of_bounds bits value hnonneg hfit

theorem valueMatchesOptionalABIType_sint256_of_bounds (value : Int)
    (hlo : -Int.ofNat (EVM.twoPow 255) ≤ value)
    (hhi : value < Int.ofNat (EVM.twoPow 255)) :
    valueMatchesOptionalABIType (some (.elem (.int (.sint ⟨256, by decide⟩))))
      (.int value) = true := by
  simp only [valueMatchesOptionalABIType, valueMatchesABIType, beq_iff_eq]
  exact normalizeInt_sint256_eq_self value hlo hhi

@[simp] theorem valueMatchesOptionalABIType_string (bytes : ByteArray) :
    valueMatchesOptionalABIType (some .string) (.bytes bytes) = true := by
  simp [valueMatchesOptionalABIType, valueMatchesABIType]

@[simp] theorem valueMatchesOptionalABIType_bytes (bytes : ByteArray) :
    valueMatchesOptionalABIType (some .bytes) (.bytes bytes) = true := by
  simp [valueMatchesOptionalABIType, valueMatchesABIType]

@[simp] theorem valueMatchesOptionalABIType_bool (value : Bool) :
    valueMatchesOptionalABIType (some (.elem .bool)) (.bool value) = true := by
  simp [valueMatchesOptionalABIType, valueMatchesABIType]

@[simp] theorem valueMatchesABIType_address (value : EVM.Address) :
    valueMatchesABIType (.elem .address) (.address value) = true := by
  simp [valueMatchesABIType]

@[simp] theorem valueMatchesOptionalABIType_address (value : EVM.Address) :
    valueMatchesOptionalABIType (some (.elem .address)) (.address value) = true :=
  valueMatchesABIType_address value

theorem valueMatchesOptionalABIType_fixedBytes (width : Fin 32) (bytes : List UInt8)
    (hlength : bytes.length = fixedBytesSize width) :
    valueMatchesOptionalABIType (some (.elem (.bytes width)))
      (.fixedBytes width bytes) = true := by
  simp [valueMatchesOptionalABIType, valueMatchesABIType, fixedBytesValid, hlength]

theorem valueMatchesABIType_uint256_ofNat {value : Nat} (hfit : value < EVM.wordModulus) :
    valueMatchesABIType (.elem (.int (.uint ⟨256, by decide⟩)))
      (.int (Int.ofNat value)) = true := by
  simp only [valueMatchesABIType, beq_iff_eq]
  apply normalizeInt_uint_eq_self
  · exact Int.natCast_nonneg value
  · exact Int.ofNat_lt.mpr hfit

theorem castValue_int (intType : IntType) (i : Int) :
    castValue? (.int i) (.elem (.int intType)) =
      some (.int (normalizeInt intType i)) := by
  cases intType <;> rfl

-- `uint256(bytes32 0x…01) = 1`; a width mismatch (`uint128(bytes32)`) is rejected.
#guard castValue? (.fixedBytes ⟨31, by decide⟩ (List.replicate 31 0 ++ [1]))
    (.elem (.int (.uint ⟨256, by decide⟩))) = some (.int 1)
#guard castValue? (.fixedBytes ⟨31, by decide⟩ (List.replicate 32 0))
    (.elem (.int (.uint ⟨128, by decide⟩))) = none
#guard castValue? (.int 511) (.elem (.int (.uint ⟨8, by decide⟩))) = some (.int 255)
#guard castValue? (.int 255) (.elem (.int (.sint ⟨8, by decide⟩))) = some (.int (-1))

def fixedBytesFromNat (n : Fin 32) (value : Nat) : Value :=
  .fixedBytes n ((EVM.Word.ofNat value).toBytesBE.drop (32 - fixedBytesSize n))

def fixedBytesBytewise? (f : UInt8 -> UInt8 -> UInt8) :
    List UInt8 -> List UInt8 -> Option (List UInt8)
  | [], [] => some []
  | x :: xs, y :: ys => do
      let rest <- fixedBytesBytewise? f xs ys
      some (f x y :: rest)
  | _, _ => none

def evalByteIndex? (bytes : List UInt8) (i : Int) : EvalResult Value :=
  if i < 0 then
    .revert
  else
    let idx := i.toNat
    if idx < bytes.length then
      EvalResult.ofOption .typeError
        (Option.map (fun b => Value.fixedBytes ⟨0, by decide⟩ [b]) (lookupNth? bytes idx))
    else
      .revert

def evalFixedBytesIndex? (n : Fin 32) (bytes : List UInt8) (i : Int) : EvalResult Value :=
  if fixedBytesValid n bytes then evalByteIndex? bytes i else .error .typeError

def normalizeRawBoolWord? : Value -> EvalResult Value
  | .tuple [.unit, .int n] =>
      if n = 0 then
        .ok (.bool false)
      else if n = 1 then
        .ok (.bool true)
      else
        .revert
  | v => .ok v

def evalIndex? (container key : Value) : EvalResult Value :=
  match container, key with
  | .array elems, .int i =>
      if 0 ≤ i ∧ i < elems.length then
        match lookupNth? elems i.toNat with
        | some v => normalizeRawBoolWord? v
        | none => .error .typeError
      else
        .revert
  | .fixedBytes n bytes, .int i => evalFixedBytesIndex? n bytes i
  | .bytes bytes, .int i => evalByteIndex? bytes.toList i
  | _, _ => .error .typeError

def evalUnaryOp? (op : UnaryOp) (v : Value) : Option Value :=
  match op, v with
  | .not, .bool b => some (.bool (!b))
  | .neg intType, .int i => some (.int (normalizeInt intType (-i)))
  | .fixedBitNot, .fixedBytes n bytes =>
      if fixedBytesValid n bytes then some (.fixedBytes n (bytes.map (fun b => ~~~b))) else none
  | .bitNot intType, .int i =>
      let bits := intType.bitWidth
      let residue := normalizeInt (.uint bits) i
      some (.int (normalizeInt intType (Int.ofNat (EVM.twoPow bits.val - 1 - residue.toNat))))
  | _, _ => none

theorem evalUnaryOp_neg_int (intType : IntType) (i : Int) :
    evalUnaryOp? (.neg intType) (.int i) =
      some (.int (normalizeInt intType (-i))) := by
  cases intType <;> rfl

#guard evalUnaryOp? (.bitNot (.uint ⟨256, by decide⟩)) (.int 0) =
  some (.int (EVM.wordModulus - 1))
#guard evalUnaryOp? (.bitNot (.uint ⟨256, by decide⟩)) (.int (EVM.wordModulus - 1)) =
  some (.int 0)
#guard evalUnaryOp? (.bitNot (.sint ⟨8, by decide⟩)) (.int (-1)) = some (.int 0)
#guard evalUnaryOp? (.neg (.sint ⟨8, by decide⟩)) (.int (-128)) = some (.int (-128))
#guard evalUnaryOp? (.neg (.sint ⟨8, by decide⟩)) (.int 1) = some (.int (-1))

def evalIntArithResult (intType : IntType) (mode : IntArithMode) (result : Int) : EvalResult Value :=
  match mode, intType with
  | .wrapping, _ => .ok (.int (normalizeInt intType result))
  | .checked, .uint bits =>
      if result < 0 || result >= Int.ofNat (EVM.twoPow bits.val) then .revert else .ok (.int result)
  | .checked, .sint bits =>
      let bound := Int.ofNat (EVM.twoPow (bits.val - 1))
      if result < -bound || result >= bound then .revert else .ok (.int result)

theorem evalIntArithResult_wrapping (intType : IntType) (result : Int) :
    evalIntArithResult intType .wrapping result = .ok (.int (normalizeInt intType result)) := by
  cases intType <;> rfl

theorem evalIntArithResult_wrapping_uint_eq_self (bits : BitWidth) (result : Int)
    (hnonneg : 0 ≤ result) (hfit : result < Int.ofNat (EVM.twoPow bits.val)) :
    evalIntArithResult (.uint bits) .wrapping result = .ok (.int result) := by
  simp only [evalIntArithResult, normalizeInt_uint_eq_self bits result hnonneg hfit]

theorem evalIntArithResult_checked_uint_ok (bits : BitWidth) (result : Int)
    (hnonneg : 0 ≤ result) (hfit : result < Int.ofNat (EVM.twoPow bits.val)) :
    evalIntArithResult (.uint bits) .checked result = .ok (.int result) := by
  simp only [evalIntArithResult]
  rw [if_neg]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
  exact ⟨Int.not_lt.mpr hnonneg, Int.not_le.mpr (by simpa using hfit)⟩

theorem evalIntArithResult_checked_uint_revert_of_neg (bits : BitWidth) (result : Int)
    (hneg : result < 0) :
    evalIntArithResult (.uint bits) .checked result = .revert := by
  simp [evalIntArithResult, hneg]

theorem evalIntArithResult_checked_uint_revert_of_overflow (bits : BitWidth) (result : Int)
    (hoverflow : Int.ofNat (EVM.twoPow bits.val) ≤ result) :
    evalIntArithResult (.uint bits) .checked result = .revert := by
  simp only [evalIntArithResult]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (by simpa using hoverflow)

theorem evalIntArithResult_checked_sint_ok (bits : BitWidth) (result : Int)
    (hlower : -Int.ofNat (EVM.twoPow (bits.val - 1)) ≤ result)
    (hupper : result < Int.ofNat (EVM.twoPow (bits.val - 1))) :
    evalIntArithResult (.sint bits) .checked result = .ok (.int result) := by
  simp only [evalIntArithResult]
  rw [if_neg]
  simp only [Bool.or_eq_true, decide_eq_true_eq, not_or]
  exact ⟨Int.not_lt.mpr hlower, Int.not_le.mpr hupper⟩

theorem evalIntArithResult_checked_sint_revert_of_underflow (bits : BitWidth)
    (result : Int) (hunderflow : result < -Int.ofNat (EVM.twoPow (bits.val - 1))) :
    evalIntArithResult (.sint bits) .checked result = .revert := by
  simp only [evalIntArithResult]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inl hunderflow

theorem evalIntArithResult_checked_sint_revert_of_overflow (bits : BitWidth)
    (result : Int) (hoverflow : Int.ofNat (EVM.twoPow (bits.val - 1)) ≤ result) :
    evalIntArithResult (.sint bits) .checked result = .revert := by
  simp only [evalIntArithResult]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr hoverflow

private def evalIntBitwise (intType : IntType) (op : Nat -> Nat -> Nat) (x y : Int) : Value :=
  let bits := intType.bitWidth
  let x := (normalizeInt (.uint bits) x).toNat
  let y := (normalizeInt (.uint bits) y).toNat
  .int (normalizeInt intType (Int.ofNat (op x y)))

def evalBinaryOp? (op : BinaryOp) (v₁ v₂ : Value) : EvalResult Value :=
  match op, v₁, v₂ with
  | .add intType mode, .int x, .int y => evalIntArithResult intType mode (x + y)
  | .sub intType mode, .int x, .int y => evalIntArithResult intType mode (x - y)
  | .mul intType mode, .int x, .int y => evalIntArithResult intType mode (x * y)
  -- division/modulo by zero reverts (Solidity Panic 0x12)
  | .div intType mode, .int x, .int y =>
      if y = 0 then .revert else evalIntArithResult intType mode (x.tdiv y)
  | .mod intType, .int x, .int y =>
      if y = 0 then .revert else evalIntArithResult intType .checked (x.tmod y)
  | .eq, .storageRef _ _, _ => .error .typeError
  | .eq, _, .storageRef _ _ => .error .typeError
  | .ne, .storageRef _ _, _ => .error .typeError
  | .ne, _, .storageRef _ _ => .error .typeError
  | .eq, x, y => .ok (.bool (x == y))
  | .ne, x, y => .ok (.bool (!(x == y)))
  | .lt, .int x, .int y => .ok (.bool (x < y))
  | .le, .int x, .int y => .ok (.bool (x <= y))
  | .gt, .int x, .int y => .ok (.bool (x > y))
  | .ge, .int x, .int y => .ok (.bool (x >= y))
  -- addresses are zero-extended words on the stack, so word-LT ≡ Nat compare of their values.
  | .lt, .address a, .address b => .ok (.bool (a.toNat < b.toNat))
  | .le, .address a, .address b => .ok (.bool (a.toNat <= b.toNat))
  | .gt, .address a, .address b => .ok (.bool (a.toNat > b.toNat))
  | .ge, .address a, .address b => .ok (.bool (a.toNat >= b.toNat))
  | .exp intType mode, .int x, .int y =>
      if y < 0 then .error .typeError else evalIntArithResult intType mode (x ^ y.toNat)
  | .lt, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        match fixedBytesToNat? n xs, fixedBytesToNat? m ys with
        | some x, some y => .ok (.bool (x < y))
        | _, _ => .error .typeError
      else .error .typeError
  | .le, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        match fixedBytesToNat? n xs, fixedBytesToNat? m ys with
        | some x, some y => .ok (.bool (x <= y))
        | _, _ => .error .typeError
      else .error .typeError
  | .gt, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        match fixedBytesToNat? n xs, fixedBytesToNat? m ys with
        | some x, some y => .ok (.bool (x > y))
        | _, _ => .error .typeError
      else .error .typeError
  | .ge, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        match fixedBytesToNat? n xs, fixedBytesToNat? m ys with
        | some x, some y => .ok (.bool (x >= y))
        | _, _ => .error .typeError
      else .error .typeError
  | .fixedBitAnd, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        if fixedBytesValid n xs && fixedBytesValid m ys then
          match fixedBytesBytewise? (· &&& ·) xs ys with
          | some zs => .ok (.fixedBytes n zs)
          | none => .error .typeError
        else .error .typeError
      else .error .typeError
  | .fixedBitOr, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        if fixedBytesValid n xs && fixedBytesValid m ys then
          match fixedBytesBytewise? (· ||| ·) xs ys with
          | some zs => .ok (.fixedBytes n zs)
          | none => .error .typeError
        else .error .typeError
      else .error .typeError
  | .fixedBitXor, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        if fixedBytesValid n xs && fixedBytesValid m ys then
          match fixedBytesBytewise? (· ^^^ ·) xs ys with
          | some zs => .ok (.fixedBytes n zs)
          | none => .error .typeError
        else .error .typeError
      else .error .typeError
  | .fixedShl, .fixedBytes n xs, .int s =>
      if s < 0 then .error .typeError
      else
        match fixedBytesToNat? n xs with
        | some x =>
            let width := 8 * fixedBytesSize n
            if s.toNat >= width then .ok (.fixedBytes n (List.replicate (fixedBytesSize n) 0))
            else .ok (fixedBytesFromNat n (x * 2 ^ s.toNat))
        | none => .error .typeError
  | .fixedShr, .fixedBytes n xs, .int s =>
      if s < 0 then .error .typeError
      else
        match fixedBytesToNat? n xs with
        | some x =>
            let width := 8 * fixedBytesSize n
            if s.toNat >= width then .ok (.fixedBytes n (List.replicate (fixedBytesSize n) 0))
            else .ok (fixedBytesFromNat n (x / 2 ^ s.toNat))
        | none => .error .typeError
  | .bitAnd intType, .int x, .int y => .ok (evalIntBitwise intType Nat.land x y)
  | .bitOr intType, .int x, .int y => .ok (evalIntBitwise intType Nat.lor x y)
  | .bitXor intType, .int x, .int y => .ok (evalIntBitwise intType Nat.xor x y)
  | .shl intType, .int x, .int s =>
      if s < 0 then .error .typeError
      else if intType.bitWidth.val <= s.toNat then .ok (.int 0)
      else .ok (.int (normalizeInt intType (x * Int.ofNat (EVM.twoPow s.toNat))))
  | .shr intType, .int x, .int s =>
      if s < 0 then .error .typeError
      else
        let x := normalizeInt intType x
        if intType.bitWidth.val <= s.toNat then
          .ok (.int (if intType.isSigned && x < 0 then -1 else 0))
        else .ok (.int (x / Int.ofNat (EVM.twoPow s.toNat)))
  | _, _, _ => .error .typeError

#guard evalBinaryOp? (.add (.uint ⟨8, by decide⟩) .checked) (.int 255) (.int 1) = .revert
#guard evalBinaryOp? (.add (.uint ⟨8, by decide⟩) .wrapping) (.int 255) (.int 1) = .ok (.int 0)
#guard evalBinaryOp? (.div (.sint ⟨8, by decide⟩) .checked) (.int (-128)) (.int (-1)) =
  .revert
#guard evalBinaryOp? (.div (.sint ⟨8, by decide⟩) .wrapping) (.int (-128)) (.int (-1)) =
  .ok (.int (-128))
#guard evalBinaryOp? (.mod (.sint ⟨8, by decide⟩)) (.int (-5)) (.int 2) =
  .ok (.int (-1))
#guard evalBinaryOp? (.bitAnd (.uint ⟨256, by decide⟩)) (.int 0xABCDEF) (.int 0xFF) =
  .ok (.int (0xABCDEF % 256))
#guard evalBinaryOp? (.bitXor (.uint ⟨8, by decide⟩)) (.int 255) (.int 2) = .ok (.int 253)
#guard evalBinaryOp? (.shl (.uint ⟨8, by decide⟩)) (.int 128) (.int 1) = .ok (.int 0)
#guard evalBinaryOp? (.shr (.sint ⟨8, by decide⟩)) (.int (-2)) (.int 1) = .ok (.int (-1))
#guard evalBinaryOp? (.exp (.uint ⟨256, by decide⟩) .checked) (.int 2) (.int 10) =
  .ok (.int 1024)
#guard evalBinaryOp? (.exp (.uint ⟨256, by decide⟩) .checked) (.int 0) (.int 0) = .ok (.int 1)
#guard evalBinaryOp? (.exp (.uint ⟨256, by decide⟩) .checked) (.int 2) (.int (-1)) =
  .error .typeError
#guard evalBinaryOp? .lt (.address (.ofNat 3)) (.address (.ofNat 5)) = .ok (.bool true)
#guard evalBinaryOp? .gt (.address (.ofNat 3)) (.address (.ofNat 5)) = .ok (.bool false)

/-- `abi.encodePacked` of an array: each element is a full 32-byte padded word, no length prefix
    (verified from solc 0.8.35 Yul IR — `add(pos, 0x20)` per element).  Elementary elements only
    (`encodeABIWord?` returns `none` for nested/dynamic element types). -/
def encodePackedArrayElems? (elemTy : ABIType) : List Value → Option (List UInt8)
  | [] => some []
  | v :: vs => do
      let w <- encodeABIWord? elemTy v
      let rest <- encodePackedArrayElems? elemTy vs
      some (EVM.Word.toBytesBE w ++ rest)

/-- Packed ("non-padded") ABI encoding of a single value, per Solidity's `abi.encodePacked`: each
    value takes its natural byte width with no left/right padding and no length prefix — `uintN`/`intN`
    are `N/8` big-endian bytes, `bool` is one byte, `address` is its 20 bytes, `bytesN` is its `N`
    bytes, and dynamic `bytes` is its raw contents.  Only the cases needed by current specs are
    handled; anything else returns `none` rather than risk a silent mis-encoding. -/
def encodePackedValue? (ty : ABIType) (v : Value) : Option (List UInt8) :=
  match ty, v with
  | .elem .bool, .bool b => some [if b then (1 : UInt8) else 0]
  | .array elemTy _, .array vs => encodePackedArrayElems? elemTy vs
  | .dynamicArray elemTy, .array vs => encodePackedArrayElems? elemTy vs
  | .elem .address, .address a => some ((EVM.word a).toBytesBE.drop 12)
  | .elem (.int (.uint bits)), .int _ => do
      let w <- encodeABIWord? ty v
      some (w.toBytesBE.drop (32 - bits.val / 8))
  | .elem (.int (.sint bits)), .int _ => do
      let w <- encodeABIWord? ty v
      some (w.toBytesBE.drop (32 - bits.val / 8))
  | .elem (.bytes n), .fixedBytes m bytes =>
      if m = n ∧ bytes.length = fixedBytesSize n then some bytes else none
  | .bytes, .bytes ba => some ba.toList
  | .string, .bytes ba => some ba.toList
  | _, _ => none

#guard encodePackedValue? (.dynamicArray (.elem (.int (.uint ⟨8, by decide⟩)))) (.array [.int 1, .int 2])
  = some (List.replicate 31 0 ++ [1] ++ List.replicate 31 0 ++ [2])

/-- `b[s:e]`: solc compiles `d[x:y]` to two `GT → REVERT` guards (verified solc 0.6.12 & 0.8.35):
    revert iff `s > e` or `e > b.size`; negative bounds are ill-typed. -/
def sliceBytes? (ba : ByteArray) (s e : Int) : EvalResult Value :=
  if s < 0 || e < 0 then .error .typeError
  else if s.toNat > e.toNat || e.toNat > ba.size then .revert
  else .ok (.bytes (ba.extract s.toNat e.toNat))

#guard sliceBytes? (ByteArray.mk #[10, 20, 30, 40, 50]) 1 3 = .ok (.bytes (ByteArray.mk #[20, 30]))
#guard sliceBytes? (ByteArray.mk #[10, 20, 30]) 0 3 = .ok (.bytes (ByteArray.mk #[10, 20, 30]))
#guard sliceBytes? (ByteArray.mk #[10, 20, 30]) 0 4 = .revert
#guard sliceBytes? (ByteArray.mk #[10, 20, 30]) 2 1 = .revert
#guard sliceBytes? (ByteArray.mk #[10, 20, 30]) 2 2 = .ok (.bytes (ByteArray.mk #[]))
#guard sliceBytes? (ByteArray.mk #[10, 20, 30]) (-1) 2 = .error .typeError

def tupleGetValue? (v : Value) (i : Nat) : EvalResult Value :=
  match v with
  | .tuple vs => match vs[i]? with | some c => .ok c | none => .error .typeError
  | _ => .error .typeError

#guard tupleGetValue? (.tuple [.int 7, .bool true]) 0 = .ok (.int 7)
#guard tupleGetValue? (.tuple [.int 7, .bool true]) 1 = .ok (.bool true)
#guard tupleGetValue? (.tuple [.int 7, .bool true]) 2 = .error .typeError
#guard tupleGetValue? (.int 7) 0 = .error .typeError

end Solm
