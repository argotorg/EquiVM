import Benchmarks.CompoundIII.Comet.Common
import Reasoning.ABI

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def priceRoundTypes : List ABIType :=
  [.elem (.int (.uint ⟨80, by decide⟩)), .elem (.int (.sint ⟨256, by decide⟩)),
    abiUInt256, abiUInt256, .elem (.int (.uint ⟨80, by decide⟩))]

def priceRoundType : ABIType := .tuple priceRoundTypes

def signedPrice (w : UInt256) : Int :=
  if w.toNat < 2^255 then Int.ofNat w.toNat else Int.ofNat w.toNat - Int.ofNat (2^256)

-- LIBRARY CANDIDATE: full-width signed words are always canonical in modern ABI decoding.
theorem decodeScalarWord_sint256_ok {bytes : List UInt8} {start : Nat}
    (hlen : ((bytes.drop start).take 32).length = 32) :
    decodeScalarWord? (.elem (.int (.sint ⟨256, by decide⟩))) bytes start =
      some (.int (signedPrice (ABI.bytesToWord ((bytes.drop start).take 32))), start + 32) := by
  simp only [decodeScalarWord?, readWord?, readBytes?, hlen, if_true, bind, Option.bind]
  change ((if (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < 2^255 then
      some (Value.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat))
    else if 2^255 ≤ (ABI.bytesToWord ((bytes.drop start).take 32)).toNat then
      some (Value.int (Int.ofNat (ABI.bytesToWord ((bytes.drop start).take 32)).toNat -
        Int.ofNat (2^256))) else none) >>= fun value ↦ some (value, start + 32)) = _
  by_cases h : (ABI.bytesToWord ((bytes.drop start).take 32)).toNat < 2^255
  · simp only [signedPrice, if_pos h, bind, Option.bind]
  · simp only [signedPrice, if_neg h, if_pos (Nat.le_of_not_gt h), bind, Option.bind]

theorem priceRoundDecode_scalar {out : ByteArray} (hhi : out.size < 2^255) :
    decodeReturnValueWithMode? .modern priceRoundType out =
      (decodeScalarWords? priceRoundTypes out.toList 0).map Value.tuple := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hvals := decodeABIValues_scalarWords_eq (types := priceRoundTypes)
    (bytes := out.toList) (cursor := 0) (total := 160) (by decide) (by decide)
  have hhead : abiTupleHeadSize? priceRoundTypes = some 160 :=
    abiTupleHeadSize_scalarWords_eq (by decide)
  have houter : abiTupleHeadSize? [priceRoundType] = some 160 := by
    simp [priceRoundType, priceRoundTypes, abiTupleHeadSize?, staticABIEncodedSize?,
      staticABIEncodedSizeList?, isDynamicABIType, isDynamicABITypeList]
  have hvalue : decodeABIValue? priceRoundType out.toList 0 =
      (do let values ← decodeScalarWords? priceRoundTypes out.toList 0
          some (.tuple values, 160)) := by
    rw [show priceRoundType = .tuple priceRoundTypes by rfl, decodeABIValue?, hhead]
    simp only [bind, Option.bind, Nat.zero_add]
    rw [hvals]
    cases decodeScalarWords? priceRoundTypes out.toList 0 <;> rfl
  change decodeReturnValue? priceRoundType out = _
  unfold decodeReturnValue? decodeReturnValues?
  rw [if_neg (by simp [hlen]; omega)]
  rw [houter]
  simp only [bind, Option.bind]
  rw [decodeABIValues?]
  rw [show isDynamicABIType priceRoundType = false by decide]
  simp only [Bool.false_eq_true, if_false]
  rw [show staticABIEncodedSize? priceRoundType = some 160 by decide]
  simp only [bind, Option.bind, Nat.zero_add]
  rw [hvalue]
  cases decodeScalarWords? priceRoundTypes out.toList 0 <;>
    simp [bind, Option.bind, decodeABIValues?]

def PriceRoundCanonical (out : ByteArray) : Prop :=
  (calldataWord out 0).toNat < 2^80 ∧ (calldataWord out 128).toNat < 2^80

instance (out : ByteArray) : Decidable (PriceRoundCanonical out) :=
  inferInstanceAs (Decidable (_ ∧ _))

def priceRoundValue (out : ByteArray) : Value :=
  .tuple [.int (calldataWord out 0).toNat, .int (signedPrice (calldataWord out 32)),
    .int (calldataWord out 64).toNat, .int (calldataWord out 96).toNat,
    .int (calldataWord out 128).toNat]

theorem priceRoundDecode_result {out : ByteArray} (hlo : 160 ≤ out.size)
    (hhi : out.size < 2^255) :
    decodeReturnValueWithMode? .modern priceRoundType out =
      if PriceRoundCanonical out then some (priceRoundValue out) else none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (off : Nat) (hb : off ≤ 128) :
      ((out.toList.drop off).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]; omega
  have hword (off : Nat) (hb : off ≤ 128) :
      ABI.bytesToWord ((out.toList.drop off).take 32) = calldataWord out off :=
    decode_word_at_eq_any out off (by omega)
  rw [priceRoundDecode_scalar hhi]
  simp only [priceRoundTypes, decodeScalarWords?,
    decodeScalarWord_uint_result ⟨80, by decide⟩ (htake 0 (by decide)),
    decodeScalarWord_sint256_ok (htake 32 (by decide)),
    decodeScalarWord_uint256_ok (htake 64 (by decide)),
    decodeScalarWord_uint256_ok (htake 96 (by decide)),
    decodeScalarWord_uint_result ⟨80, by decide⟩ (htake 128 (by decide)),
    hword 0 (by decide), hword 32 (by decide), hword 64 (by decide),
    hword 96 (by decide), hword 128 (by decide)]
  by_cases h0 : (calldataWord out 0).toNat < 2^80 <;>
    by_cases h4 : (calldataWord out 128).toNat < 2^80 <;>
    simp only [PriceRoundCanonical, EVM.twoPow, h0, h4, and_self, and_true,
      and_false, ite_true, ite_false, bind, Option.bind, Option.map]; rfl

theorem priceRoundDecode_short {out : ByteArray} (hshort : out.size < 160) :
    decodeReturnValueWithMode? .modern priceRoundType out = none := by
  rw [priceRoundDecode_scalar (by omega)]
  have hnone : decodeScalarWords? priceRoundTypes out.toList 0 = none := by
    cases h : decodeScalarWords? priceRoundTypes out.toList 0 with
    | none => rfl
    | some vs =>
        have hb := decodeScalarWords?_some_length (Nat.zero_le _) h
        have hlen : out.toList.length = out.size := by
          rw [byteArray_toList_eq, Array.length_toList]; rfl
        change 0 + 32 * 5 ≤ out.toList.length at hb
        omega
  rw [hnone]; rfl

end Benchmarks.CompoundIII.Comet
