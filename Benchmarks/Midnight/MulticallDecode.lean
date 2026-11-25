import Benchmarks.Midnight.MulticallArrayValue
import Benchmarks.Midnight.CalldataArgumentSlice

/-! The external multicall argument and its direct-calldata ABI policy. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def multicallArguments (calls : List ByteArray) : Store :=
  (∅ : Store).insert "calls" (.array (calls.map Value.bytes))

def decodeMulticallArguments (bytes : ByteArray) : Option Store :=
  if CalldataArgumentValid false bytes 4 then
    (decodeMulticallTails bytes (calldataArgumentPointer bytes 4) 0
      (calldataArgumentLength bytes 4).toNat).map multicallArguments
  else none

theorem midnightDecodeMulticall_none_check {bytes : ByteArray}
    (h4 : 4 ≤ bytes.size) (hcheck : solcSLT (solcSub bytes.size 4) 32 = true) :
    config.externalABI.decodeCalldata? ["calls"] [.dynamicArray .bytes] bytes = none := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  change Model.decodeCalldata _ _ bytes = _
  simp only [Model.decodeCalldata, decodeCalldataWithMode, decodeCalldata, hl,
    show ¬ bytes.size < 4 from by omega, if_false, Model.calldataMode, List.any_cons,
    List.any_nil, isDynamicABIType, Bool.true_or, decodeArgs?, List.isEmpty_cons,
    Bool.false_eq_true, abiTupleHeadSize?, staticABIEncodedSize?, bind, Option.bind,
    hcheck, if_true, ite_self]

theorem decodeSolcMulticall {bytes : ByteArray}
    (h36 : 36 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : (bytesToWord (bytes.toList.take 4)).toNat = 0xac9650d8)
    (hcheck : solcSLT (solcSub bytes.size 4) 32 = false) :
    decodeCalldataWithMode Model.calldataMode ["calls"] [.dynamicArray .bytes] bytes =
      decodeMulticallArguments bytes := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeCalldataWithMode, decodeCalldata, hl, show ¬ bytes.size < 4 from by omega,
    if_false, Model.calldataMode, List.any_cons, List.any_nil, isDynamicABIType, Bool.true_or,
    decodeArgs?, List.isEmpty_cons, Bool.false_eq_true, abiTupleHeadSize?, staticABIEncodedSize?,
    bind, Option.bind, Nat.reduceAdd, if_true, hcheck, ite_self]
  have hp : ((([(0xac9650d8, [{ materialize := [] }])] : List (Nat × List CalldataPlan)).find?
      (fun entry ↦ entry.1 == (bytesToWord (bytes.toList.take 4)).toNat)).map Prod.snd).getD [] =
      [{ materialize := [] }] := by simp [hselector, List.find?]
  rw [hp, decodeFields?]
  simp only [stride?, isDynamicABIType, if_true, bind, Option.bind, List.headD_cons,
    retainFailure, show ({ materialize := [] } : CalldataPlan).deferErrors.contains [] = false
      from rfl, Bool.false_eq_true, if_false, Bool.not_true, Bool.and_false,
    solcTailTarget?, solcAdd, Nat.add_zero,
    show 4 % EVM.wordModulus = 4 from by decide,
    solcReadNat_bounded (by omega : 4 + 32 ≤ bytes.size) hsize]
  unfold decodeMulticallArguments
  by_cases ho : (calldataWord bytes 4).toNat < 2^64
  · have hmax : ¬ solcMaxU64 < (calldataWord bytes 4).toNat := by
      change ¬ (2^64 - 1 < _); omega
    have hstart : 4 + (calldataWord bytes 4).toNat < 2^128 := by omega
    have ha : (4 + (calldataWord bytes 4).toNat) % EVM.wordModulus =
        4 + (calldataWord bytes 4).toNat := Nat.mod_eq_of_lt (by change _ < 2^256; omega)
    simp only [hmax, if_false, ha]
    rw [solcMulticallArrayValue hsize hstart]
    have hh := calldataArgumentHead_toNat (bytes := bytes) (slot := 4) ho
    have hptr : calldataArgumentPointer bytes 4 =
        UInt256.ofNat (4 + (calldataWord bytes 4).toNat + 32) := by
      apply u256_inj
      rw [calldataArgumentPointer, uadd_word_ofNat_toNat _ _ (by
        rw [hh]; change _ < 2^256; omega), hh,
        UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
    simp only [CalldataArgumentValid, ho, true_and, CalldataSliceValid,
      show calldataSliceStride false = 32 from rfl, hh]
    change _ = if bytes.size < 2^255 ∧ 4 + (calldataWord bytes 4).toNat + 32 ≤ bytes.size ∧
        (calldataWord bytes (4 + (calldataWord bytes 4).toNat)).toNat < 2^64 ∧
        4 + (calldataWord bytes 4).toNat + 32 +
          32 * (calldataWord bytes (4 + (calldataWord bytes 4).toNat)).toNat ≤ bytes.size then _ else _
    split_ifs
    · simp only [if_true, bind, Option.bind, decodeFields?, List.tail_cons,
        hptr, calldataArgumentLength, hh]
      cases decodeMulticallTails bytes
        (UInt256.ofNat (4 + (calldataWord bytes 4).toNat + 32)) 0
        (calldataWord bytes (4 + (calldataWord bytes 4).toNat)).toNat <;> rfl
    · simp only [if_false, bind, Option.bind]
  · have hmax : solcMaxU64 < (calldataWord bytes 4).toNat := by
      change 2^64 - 1 < _; omega
    have hv : ¬ CalldataArgumentValid false bytes 4 := fun h ↦ ho h.1
    simp only [hmax, if_true, if_neg hv, bind, Option.bind]

theorem midnightDecodeMulticall {bytes : ByteArray}
    (h36 : 36 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hselector : (bytesToWord (bytes.toList.take 4)).toNat = 0xac9650d8)
    (hcheck : solcSLT (solcSub bytes.size 4) 32 = false) :
    config.externalABI.decodeCalldata? ["calls"] [.dynamicArray .bytes] bytes =
      decodeMulticallArguments bytes := by
  change Model.decodeCalldata _ _ bytes = _
  unfold Model.decodeCalldata
  rw [decodeSolcMulticall h36 hsize hselector hcheck]
  unfold decodeMulticallArguments
  split
  · cases decodeMulticallTails bytes (calldataArgumentPointer bytes 4) 0
      (calldataArgumentLength bytes 4).toNat with
    | none => rfl
    | some calls => simp [multicallArguments, Model.inputSizesFit]
  · rfl

end Benchmarks.Midnight
