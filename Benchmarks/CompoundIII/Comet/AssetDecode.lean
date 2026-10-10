import Benchmarks.CompoundIII.Comet.ScalarTupleDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def assetInfoTypes : List ABIType :=
  [.elem (.int (.uint ⟨8, by decide⟩)), abiAddress, abiAddress,
    .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨64, by decide⟩)),
    .elem (.int (.uint ⟨128, by decide⟩))]

def assetInfoType : ABIType := .tuple assetInfoTypes

def AssetCanonical (out : ByteArray) : Prop :=
  (calldataWord out 0).toNat < 2^8 ∧
  (calldataWord out 32).toNat < 2^160 ∧
  (calldataWord out 64).toNat < 2^160 ∧
  (calldataWord out 96).toNat < 2^64 ∧
  (calldataWord out 128).toNat < 2^64 ∧
  (calldataWord out 160).toNat < 2^64 ∧
  (calldataWord out 192).toNat < 2^64 ∧
  (calldataWord out 224).toNat < 2^128

instance (out : ByteArray) : Decidable (AssetCanonical out) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

def assetTuple (out : ByteArray) : Value :=
  .tuple [.int (calldataWord out 0).toNat,
    .address (AccountAddress.ofNat (calldataWord out 32).toNat),
    .address (AccountAddress.ofNat (calldataWord out 64).toNat),
    .int (calldataWord out 96).toNat, .int (calldataWord out 128).toNat,
    .int (calldataWord out 160).toNat, .int (calldataWord out 192).toNat,
    .int (calldataWord out 224).toNat]

theorem assetDecode_scalar {out : ByteArray} (hhi : out.size < 2^255) :
    decodeReturnValueWithMode? .modern assetInfoType out =
      (decodeScalarWords? assetInfoTypes out.toList 0).map Value.tuple :=
  decodeReturnValue_scalarTuple (by decide) hhi

theorem assetDecode_result {out : ByteArray} (hlo : 256 ≤ out.size)
    (hhi : out.size < 2^255) :
    decodeReturnValueWithMode? .modern assetInfoType out =
      if AssetCanonical out then some (assetTuple out) else none := by
  have hlen : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have htake (off : Nat) (hb : off ≤ 224) :
      ((out.toList.drop off).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, hlen]; omega
  have hword (off : Nat) (hb : off ≤ 224) :
      ABI.bytesToWord ((out.toList.drop off).take 32) = calldataWord out off :=
    decode_word_at_eq_any out off (by omega)
  rw [assetDecode_scalar hhi]
  simp only [assetInfoTypes, decodeScalarWords?, abiAddress,
    decodeScalarWord_uint_result ⟨8, by decide⟩ (htake 0 (by decide)),
    decodeScalarWord_address_result (htake 32 (by decide)),
    decodeScalarWord_address_result (htake 64 (by decide)),
    decodeScalarWord_uint_result ⟨64, by decide⟩ (htake 96 (by decide)),
    decodeScalarWord_uint_result ⟨64, by decide⟩ (htake 128 (by decide)),
    decodeScalarWord_uint_result ⟨64, by decide⟩ (htake 160 (by decide)),
    decodeScalarWord_uint_result ⟨64, by decide⟩ (htake 192 (by decide)),
    decodeScalarWord_uint_result ⟨128, by decide⟩ (htake 224 (by decide)),
    hword 0 (by decide), hword 32 (by decide), hword 64 (by decide),
    hword 96 (by decide), hword 128 (by decide), hword 160 (by decide),
    hword 192 (by decide), hword 224 (by decide)]
  simp only [AssetCanonical, assetTuple, EVM.twoPow, EVM.addressModulus, ite_and]
  by_cases h0 : (calldataWord out 0).toNat < 2^8 <;>
    simp only [h0, ite_true, ite_false, bind, Option.bind, Option.map]
  by_cases h32 : (calldataWord out 32).toNat < 2^160 <;>
    simp only [h32, ite_true, ite_false]
  by_cases h64 : (calldataWord out 64).toNat < 2^160 <;>
    simp only [h64, ite_true, ite_false]
  by_cases h96 : (calldataWord out 96).toNat < 2^64 <;>
    simp only [h96, ite_true, ite_false]
  by_cases h128 : (calldataWord out 128).toNat < 2^64 <;>
    simp only [h128, ite_true, ite_false]
  by_cases h160 : (calldataWord out 160).toNat < 2^64 <;>
    simp only [h160, ite_true, ite_false]
  by_cases h192 : (calldataWord out 192).toNat < 2^64 <;>
    simp only [h192, ite_true, ite_false]
  by_cases h224 : (calldataWord out 224).toNat < 2^128 <;>
    simp only [h224, ite_true, ite_false]
  rfl

theorem assetDecode_short {out : ByteArray} (hshort : out.size < 256) :
    decodeReturnValueWithMode? .modern assetInfoType out = none := by
  rw [assetDecode_scalar (by omega)]
  have hnone : decodeScalarWords? assetInfoTypes out.toList 0 = none := by
    cases h : decodeScalarWords? assetInfoTypes out.toList 0 with
    | none => rfl
    | some vs =>
        have hb := decodeScalarWords?_some_length (Nat.zero_le _) h
        have hlen : out.toList.length = out.size := by
          rw [byteArray_toList_eq, Array.length_toList]; rfl
        change 0 + 32 * 8 ≤ out.toList.length at hb
        omega
  rw [hnone]; rfl

end Benchmarks.CompoundIII.Comet
