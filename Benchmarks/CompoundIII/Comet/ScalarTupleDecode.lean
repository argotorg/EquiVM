import Benchmarks.CompoundIII.Comet.Common
import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: flattening the modern return decoder for a tuple of scalar words.
theorem scalarTuple_static {types : List ABIType}
    (hs : types.all isABIScalarWordType = true) (acc : Nat) :
    isDynamicABITypeList types = false ∧
      staticABIEncodedSizeList? types acc = some (acc + 32 * types.length) := by
  induction types generalizing acc with
  | nil => simp [isDynamicABITypeList, staticABIEncodedSizeList?]
  | cons ty tys ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hs
      have hd := isABIScalarWordType_dynamic hs.1
      have hz := isABIScalarWordType_size hs.1
      simp [isDynamicABITypeList, staticABIEncodedSizeList?, hd, hz,
        (ih hs.2 acc).1, (ih hs.2 (acc + 32)).2,
        Nat.mul_add, Nat.add_assoc, Nat.add_comm]

theorem decodeReturnValue_scalarTuple {types : List ABIType} {out : ByteArray}
    (hs : types.all isABIScalarWordType = true) (hhi : out.size < 2^255) :
    decodeReturnValueWithMode? .modern (.tuple types) out =
      (decodeScalarWords? types out.toList 0).map Value.tuple := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hvals := decodeABIValues_scalarWords_eq
    (bytes := out.toList) (cursor := 0) hs (Nat.zero_add _)
  have hhead := abiTupleHeadSize_scalarWords_eq hs
  have hd : isDynamicABIType (.tuple types) = false := (scalarTuple_static hs 0).1
  have hz : staticABIEncodedSize? (.tuple types) = some (32 * types.length) := by
    simpa only [staticABIEncodedSize?, Nat.zero_add] using (scalarTuple_static hs 0).2
  have houter : abiTupleHeadSize? [.tuple types] = some (32 * types.length) := by
    simp [abiTupleHeadSize?, hd, hz]
  have hvalue : decodeABIValue? (.tuple types) out.toList 0 =
      (do let values ← decodeScalarWords? types out.toList 0
          some (.tuple values, 32 * types.length)) := by
    rw [decodeABIValue?, hhead]
    simp only [bind, Option.bind, Nat.zero_add]
    rw [hvals]
    cases decodeScalarWords? types out.toList 0 <;> rfl
  change decodeReturnValue? (.tuple types) out = _
  unfold decodeReturnValue? decodeReturnValues?
  rw [if_neg (by simp [hlen]; omega), houter]
  simp only [bind, Option.bind]
  rw [decodeABIValues?, hd]
  simp only [Bool.false_eq_true, if_false]
  rw [hz]
  simp only [bind, Option.bind, Nat.zero_add]
  rw [hvalue]
  cases decodeScalarWords? types out.toList 0 <;>
    simp [bind, Option.bind, decodeABIValues?]

-- LIBRARY CANDIDATE: one conditional form covering both canonical address branches.
theorem decodeScalarWord_address_result {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? (.elem .address) bytes start =
      if (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < EVM.addressModulus then
        some (.address (AccountAddress.ofNat
          (ABI.bytesToWord ((bytes.drop start).take 32)).toNat), start + 32)
      else none := by
  split_ifs with h
  · exact decodeScalarWord_address_ok hlen h
  · exact decodeScalarWord_address_none_noncanon hlen h

end Benchmarks.CompoundIII.Comet
