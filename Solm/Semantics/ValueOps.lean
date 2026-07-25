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
  | .elem (.int _), .int _ => some v
  | .contract _, .address _ => some v
  | .struct expected _, .struct actual _ =>
      if expected = actual then some v else none
  | .array _ _, .array _ => some v
  | .dynamicArray _, .array _ => some v
  | _, _ => none

-- `uint256(bytes32 0x…01) = 1`; a width mismatch (`uint128(bytes32)`) is rejected.
#guard castValue? (.fixedBytes ⟨31, by decide⟩ (List.replicate 31 0 ++ [1]))
    (.elem (.int (.uint ⟨256, by decide⟩))) = some (.int 1)
#guard castValue? (.fixedBytes ⟨31, by decide⟩ (List.replicate 32 0))
    (.elem (.int (.uint ⟨128, by decide⟩))) = none

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
  | .neg, .int i => some (.int (-i))
  | .bitNot, .fixedBytes n bytes =>
      if fixedBytesValid n bytes then some (.fixedBytes n (bytes.map (fun b => ~~~b))) else none
  -- `~x` on an int is the word complement, defined only on `[0, 2^256)`.
  | .bitNot, .int x =>
      if 0 ≤ x ∧ x < (EVM.wordModulus : Int) then some (.int (EVM.wordModulus - 1 - x.toNat))
      else none
  | _, _ => none

#guard evalUnaryOp? .bitNot (.int 0) = some (.int (EVM.wordModulus - 1))
#guard evalUnaryOp? .bitNot (.int (EVM.wordModulus - 1)) = some (.int 0)
#guard evalUnaryOp? .bitNot (.int (-1)) = none

def evalBinaryOp? (op : BinaryOp) (v₁ v₂ : Value) : EvalResult Value :=
  match op, v₁, v₂ with
  | .add, .int x, .int y => .ok (.int (x + y))
  | .sub, .int x, .int y => .ok (.int (x - y))
  | .mul, .int x, .int y => .ok (.int (x * y))
  -- division/modulo by zero reverts (Solidity Panic 0x12)
  | .div, .int x, .int y => if y = 0 then .revert else .ok (.int (x / y))
  | .mod, .int x, .int y => if y = 0 then .revert else .ok (.int (x % y))
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
  -- `x ** y`: exact integer power; exponent must be ≥ 0 (spec wraps `% 2^N` by hand, like add/mul).
  | .exp, .int x, .int y => if y < 0 then .error .typeError else .ok (.int (x ^ y.toNat))
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
  | .bitAnd, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        if fixedBytesValid n xs && fixedBytesValid m ys then
          match fixedBytesBytewise? (· &&& ·) xs ys with
          | some zs => .ok (.fixedBytes n zs)
          | none => .error .typeError
        else .error .typeError
      else .error .typeError
  | .bitOr, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        if fixedBytesValid n xs && fixedBytesValid m ys then
          match fixedBytesBytewise? (· ||| ·) xs ys with
          | some zs => .ok (.fixedBytes n zs)
          | none => .error .typeError
        else .error .typeError
      else .error .typeError
  | .bitXor, .fixedBytes n xs, .fixedBytes m ys =>
      if n = m then
        if fixedBytesValid n xs && fixedBytesValid m ys then
          match fixedBytesBytewise? (· ^^^ ·) xs ys with
          | some zs => .ok (.fixedBytes n zs)
          | none => .error .typeError
        else .error .typeError
      else .error .typeError
  | .shl, .fixedBytes n xs, .int s =>
      if s < 0 then .error .typeError
      else
        match fixedBytesToNat? n xs with
        | some x =>
            let width := 8 * fixedBytesSize n
            if s.toNat >= width then .ok (.fixedBytes n (List.replicate (fixedBytesSize n) 0))
            else .ok (fixedBytesFromNat n (x * 2 ^ s.toNat))
        | none => .error .typeError
  | .shr, .fixedBytes n xs, .int s =>
      if s < 0 then .error .typeError
      else
        match fixedBytesToNat? n xs with
        | some x =>
            let width := 8 * fixedBytesSize n
            if s.toNat >= width then .ok (.fixedBytes n (List.replicate (fixedBytesSize n) 0))
            else .ok (fixedBytesFromNat n (x / 2 ^ s.toNat))
        | none => .error .typeError
  -- Integer bitwise/shift: defined only on operands in `[0, 2^256)`; a negative or oversized
  -- operand is `.error .typeError`, so specs on signed values must re-encode to a word first.
  | .bitAnd, .int x, .int y =>
      if 0 ≤ x ∧ x < (EVM.wordModulus : Int) ∧ 0 ≤ y ∧ y < (EVM.wordModulus : Int) then
        .ok (.int (Nat.land x.toNat y.toNat))
      else .error .typeError
  | .bitOr, .int x, .int y =>
      if 0 ≤ x ∧ x < (EVM.wordModulus : Int) ∧ 0 ≤ y ∧ y < (EVM.wordModulus : Int) then
        .ok (.int (Nat.lor x.toNat y.toNat))
      else .error .typeError
  | .bitXor, .int x, .int y =>
      if 0 ≤ x ∧ x < (EVM.wordModulus : Int) ∧ 0 ≤ y ∧ y < (EVM.wordModulus : Int) then
        .ok (.int (Nat.xor x.toNat y.toNat))
      else .error .typeError
  -- `x << s`: the shift `s` must be a non-negative int; `s ≥ 256` gives `0` (EVM `SHL`).
  | .shl, .int x, .int s =>
      if 0 ≤ x ∧ x < (EVM.wordModulus : Int) ∧ 0 ≤ s then
        if (256 : Int) ≤ s then .ok (.int 0)
        else .ok (.int ((x.toNat * 2 ^ s.toNat) % EVM.wordModulus))
      else .error .typeError
  -- `x >> s`: the shift `s` must be a non-negative int; `s ≥ 256` gives `0` (EVM `SHR`).
  | .shr, .int x, .int s =>
      if 0 ≤ x ∧ x < (EVM.wordModulus : Int) ∧ 0 ≤ s then
        if (256 : Int) ≤ s then .ok (.int 0)
        else .ok (.int (x.toNat / 2 ^ s.toNat))
      else .error .typeError
  | _, _, _ => .error .typeError

-- Bitwise mask = mod; single-bit xor flip; `shl` wraps at the top word; `shr` of the max word;
-- and a negative operand is a type error.
#guard evalBinaryOp? .bitAnd (.int 0xABCDEF) (.int 0xFF) = .ok (.int (0xABCDEF % 256))
#guard evalBinaryOp? .bitXor (.int 5) (.int 2) = .ok (.int 7)
#guard evalBinaryOp? .shl (.int (2 ^ 255)) (.int 1) = .ok (.int 0)
#guard evalBinaryOp? .shr (.int (2 ^ 256 - 1)) (.int 255) = .ok (.int 1)
#guard evalBinaryOp? .bitAnd (.int (-1)) (.int 0) = .error .typeError
#guard evalBinaryOp? .exp (.int 2) (.int 10) = .ok (.int 1024)
#guard evalBinaryOp? .exp (.int 0) (.int 0) = .ok (.int 1)
#guard evalBinaryOp? .exp (.int 2) (.int (-1)) = .error .typeError
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
