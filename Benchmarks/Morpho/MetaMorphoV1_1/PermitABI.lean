import Benchmarks.Morpho.MetaMorphoV1_1.PermitData
import Benchmarks.Morpho.MetaMorphoV1_1.CalldataValueDecode

/-! Exact decoding conditions for the seven permit calldata fields. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

set_option maxRecDepth 2000

def permitNames : List Ident := ["owner", "spender", "value", "deadline", "v", "r", "s"]

def permitTypes : List ABIType :=
  [abiAddress, abiAddress, abiUInt256, abiUInt256, .elem (.int (.uint ⟨8, by decide⟩)),
    abiBytes32, abiBytes32]

def permitCalldataData (cd : ByteArray) : PermitData :=
  ⟨AccountAddress.ofNat (calldataWord cd 4).toNat,
    AccountAddress.ofNat (calldataWord cd 36).toNat, calldataWord cd 68, calldataWord cd 100,
    calldataWord cd 132, calldataWord cd 164, calldataWord cd 196⟩

def PermitChecks (cd : ByteArray) : Prop :=
  (calldataWord cd 4).toNat < EVM.addressModulus ∧
    (calldataWord cd 36).toNat < EVM.addressModulus ∧ (calldataWord cd 132).toNat < 256

instance (cd : ByteArray) : Decidable (PermitChecks cd) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

private theorem permitValuesDecode {cd : ByteArray} (hlen : 228 ≤ cd.size) :
    decodeABIValues? permitTypes (cd.toList.drop 4) 0 0 224 224 =
      if PermitChecks cd then
        some ([.address (permitCalldataData cd).owner, .address (permitCalldataData cd).spender,
          uint256Value (permitCalldataData cd).value,
          uint256Value (permitCalldataData cd).deadline,
          uint256Value (permitCalldataData cd).sigV,
          wordBytes32Value (permitCalldataData cd).sigR,
          wordBytes32Value (permitCalldataData cd).sigS], 224)
      else none := by
  have ha0 := decodeCalldataAddressField (cd := cd) (off := 0) (by omega)
  have ha32 := decodeCalldataAddressField (cd := cd) (off := 32) (by omega)
  have hu64 := decodeCalldataWordField (cd := cd) (off := 64) (by omega)
  have hu96 := decodeCalldataWordField (cd := cd) (off := 96) (by omega)
  have hu128 := decodeCalldataUintField (cd := cd) (off := 128) ⟨8, by decide⟩ (by omega)
  have hb160 := decodeCalldataBytes32Field (cd := cd) (off := 160) (by omega)
  have hb192 := decodeCalldataBytes32Field (cd := cd) (off := 192) (by omega)
  simp only [Nat.reduceAdd, EVM.twoPow, abiAddress, abiUInt256, abiBytes32,
    abiBytes32Width] at ha0 ha32 hu64 hu96 hu128 hb160 hb192
  change decodeABIValue? (.elem (.bytes 31)) (cd.toList.drop 4) 160 =
    some (wordBytes32Value (calldataWord cd 164), 192) at hb160
  change decodeABIValue? (.elem (.bytes 31)) (cd.toList.drop 4) 192 =
    some (wordBytes32Value (calldataWord cd 196), 224) at hb192
  by_cases h0 : (calldataWord cd 4).toNat < EVM.addressModulus <;>
    by_cases h32 : (calldataWord cd 36).toNat < EVM.addressModulus <;>
    by_cases h128 : (calldataWord cd 132).toNat < 256
  all_goals
    simp only [permitTypes]
    repeat'
      rw [decodeABIValues?]
      simp [abiAddress, abiUInt256, abiBytes32, abiBytes32Width, isDynamicABIType,
        staticABIEncodedSize?, ha0, ha32, hu64, hu96, hu128, hb160, hb192,
        h0, h32, h128, PermitChecks, permitCalldataData]

theorem permitDecodeLong {cd : ByteArray} (hlen : 228 ≤ cd.size)
    (hhi : cd.size < 2 ^ 255 + 4) :
    decodeCalldata permitNames permitTypes cd =
      if PermitChecks cd then some (permitCalldataData cd).locals else none := by
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [hl]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [permitTypes, abiAddress, abiUInt256, abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, h⟩; rw [List.length_drop, hl] at h; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard, permitTypes])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? permitTypes = some 224 from by native_decide]
  simp only [bind, Option.bind]
  rw [if_neg (by rw [List.length_drop, hl]; omega : ¬ (cd.toList.drop 4).length < 224)]
  rw [permitValuesDecode hlen]
  by_cases hc : PermitChecks cd <;>
    simp [hc, permitNames, permitTypes, decodeCalldata.insertValues, PermitData.locals]

theorem permitDecodeShort {cd : ByteArray} (hlen : cd.size < 228) :
    decodeCalldata permitNames permitTypes cd = none := by
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  by_cases h4 : cd.toList.length < 4
  · rw [if_pos h4]
  rw [if_neg h4]
  rw [if_neg (by simp [permitTypes, abiAddress, abiUInt256, abiBytes32, isDynamicABIType])]
  rw [if_neg (by rintro ⟨_, h⟩; rw [List.length_drop, hl] at h; omega)]
  rw [if_neg (by simp [solcTotalSizeDynamicGuard, permitTypes])]
  simp only [decodeCalldata.decodeArgs]
  rw [show abiTupleHeadSize? permitTypes = some 224 from by native_decide]
  simp only [bind, Option.bind]
  rw [if_pos (by rw [List.length_drop, hl]; omega : (cd.toList.drop 4).length < 224)]
  rfl

theorem permitDecodeHuge {cd : ByteArray} (hhi : 2 ^ 255 + 4 ≤ cd.size) :
    decodeCalldata permitNames permitTypes cd = none := by
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  unfold decodeCalldata
  rw [if_neg (by rw [hl]; omega : ¬ cd.toList.length < 4)]
  rw [if_neg (by simp [permitTypes, abiAddress, abiUInt256, abiBytes32, isDynamicABIType])]
  rw [if_pos ⟨rfl, by rw [List.length_drop, hl]; omega⟩]

end Benchmarks.Morpho.MetaMorphoV1_1
