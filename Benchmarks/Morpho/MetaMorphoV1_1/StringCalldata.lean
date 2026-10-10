import Reasoning.ABIViews

/-! Source decoding and payload representation for one dynamic string parameter. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: reusable names and bounds for the one-string ABI layout.
def calldataStringLength (cd : ByteArray) : UInt256 :=
  calldataWord cd (4 + (calldataWord cd 4).toNat)

def calldataStringStart (cd : ByteArray) : UInt256 := calldataWord cd 4 + ⟨36⟩

def calldataStringBytes (cd : ByteArray) : ByteArray :=
  cd.extract ((calldataWord cd 4).toNat + 36)
    ((calldataWord cd 4).toNat + 36 + (calldataStringLength cd).toNat)

theorem calldataStringStart_toNat (cd : ByteArray)
    (hoff : (calldataWord cd 4).toNat < 2 ^ 64) :
    (calldataStringStart cd).toNat = (calldataWord cd 4).toNat + 36 :=
  uadd_word_ofNat_toNat _ 36 (by change _ < 2 ^ 256; omega)

theorem calldataStringBytes_size (cd : ByteArray)
    (hpayload : (calldataWord cd 4).toNat + 36 + (calldataStringLength cd).toNat ≤ cd.size) :
    (calldataStringBytes cd).size = (calldataStringLength cd).toNat := by
  simp only [calldataStringBytes, ByteArray.size_extract]
  omega

theorem calldataStringBytes_list (cd : ByteArray) :
    calldataStringBytes cd = ByteArray.mk
      ((((cd.toList.drop 4).drop ((calldataWord cd 4).toNat + 32)).take
        (calldataStringLength cd).toNat).toArray) := by
  apply byteArray_eq_of_toList_eq
  simp [calldataStringBytes, byteArray_extract_toList, byteArray_toList_eq, List.drop_drop,
    show 4 + ((calldataWord cd 4).toNat + 32) = (calldataWord cd 4).toNat + 36 by omega]

theorem decodeCalldataString (cd : ByteArray) (param : Ident)
    (hhead : 36 ≤ cd.size) (hsize : cd.size < 2 ^ 255)
    (hoff : (calldataWord cd 4).toNat < 2 ^ 64)
    (hpayload : (calldataWord cd 4).toNat + 36 + (calldataStringLength cd).toNat ≤ cd.size)
    (hlen : (calldataStringLength cd).toNat < 2 ^ 64) :
    decodeCalldata [param] [.string] cd =
      some ((∅ : Store).insert param (.bytes (calldataStringBytes cd))) := by
  rw [calldataStringBytes_list]
  apply decodeCalldata_string_some hhead hsize
  · unfold solcMaxU64; omega
  · omega
  · change ¬ solcMaxU64 < (calldataStringLength cd).toNat
    unfold solcMaxU64; omega
  · simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min _ (cd.size - 4 - _) = _
    exact min_eq_left (by change (calldataStringLength cd).toNat ≤ _; omega)

-- GENERALIZES the head-short string branch from the StringStoreLite example.
theorem decodeCalldataStringShort (cd : ByteArray) (param : Ident)
    (hshort : cd.size < 36) : decodeCalldata [param] [.string] cd = none := by
  unfold decodeCalldata
  have htlen : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  by_cases h4 : cd.toList.length < 4
  · rw [if_pos h4]
  · rw [if_neg h4]
    have hnotDyn : ¬ ([ABIType.string].any isDynamicABIType = true ∧
        2 ^ 255 ≤ cd.toList.length) := by omega
    have hnotHuge : ¬ ([ABIType.string].isEmpty = false ∧
        2 ^ 255 ≤ (cd.toList.drop 4).length) := by rw [List.length_drop]; omega
    have hnotTotal : ¬ (solcTotalSizeDynamicGuard [ABIType.string] = true ∧
        2 ^ 255 ≤ cd.toList.length) := by omega
    rw [if_neg hnotDyn, if_neg hnotHuge, if_neg hnotTotal]
    simp [decodeCalldata.decodeArgs, abiTupleHeadSize?, isDynamicABIType, htlen,
      show cd.size - 4 < 32 by omega]

end Benchmarks.Morpho.MetaMorphoV1_1
