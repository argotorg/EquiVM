import Benchmarks.CompoundIII.Comet.ConstructorDataMemory
import Benchmarks.CompoundIII.Comet.CreationBlocks_004

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorInitialImmMemory (c : ConstructorConfig) (w : UInt256)
    (mem : ByteArray) : ByteArray :=
  let mem := writeWord mem 128 (constructorRecordWord c 0)
  let mem := writeWord mem 160 (constructorRecordWord c 1)
  let mem := writeWord mem 192 (constructorRecordWord c 2)
  let mem := writeWord mem 224 (constructorRecordWord c 3)
  let mem := writeWord mem 256 (constructorRecordWord c 4)
  let mem := writeWord mem 544 (constructorRecordWord c 13)
  writeWord mem 800 w

theorem constructorRecordWord_addressCanonical (c : ConstructorConfig) {j : Nat} (hj : j < 5) :
    (constructorRecordWord c j).toNat < 2^160 := by
  interval_cases j <;> exact constructorAddressScalar_canonical _

theorem constructorRecordWord_uint64Canonical (c : ConstructorConfig) {j : Nat}
    (hlo : 5 ≤ j) (hhi : j < 17) : (constructorRecordWord c j).toNat < 2^64 := by
  interval_cases j <;> exact constructorUintScalar_canonical ⟨64, by decide⟩ _

theorem constructorInitialImmMemory_data {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem) (w : UInt256) :
    ConstructorDataMemory c (constructorInitialImmMemory c w mem) := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  unfold constructorInitialImmMemory
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  apply ConstructorDataMemory.writeBelow _ _ (by omega)
  exact hm.writeBelow _ (by omega)

theorem constructorInitialImmMemory_eq {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) (w : UInt256) :
    cometWithExtendedAssetListCreation_block_902_memory (mem := mem) (x0 := w)
      (x1 := UInt256.ofNat (constructorRecordBase c)) = constructorInitialImmMemory c w mem := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  have h0 := hm.scalar (j := 0) (by decide) hsize
  have ha (j : Nat) (hj : j < 5) : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (constructorRecordWord c j) = constructorRecordWord c j := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by native_decide)
      (constructorRecordWord_addressCanonical c hj)
  have hf : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
      (constructorRecordWord c 13) = constructorRecordWord c 13 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 64) _ _ (by native_decide)
      (constructorRecordWord_uint64Canonical c (by decide) (by decide))
  have h1 := hm.writeBelow (constructorRecordWord c 0) (off := 128) (by omega)
  have h2 := h1.writeBelow (constructorRecordWord c 1) (off := 160) (by omega)
  have h3 := h2.writeBelow (constructorRecordWord c 2) (off := 192) (by omega)
  have h4 := h3.writeBelow (constructorRecordWord c 3) (off := 224) (by omega)
  have h5 := h4.writeBelow (constructorRecordWord c 4) (off := 256) (by omega)
  have hr0 : memLoad (UInt256.ofNat (constructorRecordBase c)) mem = constructorRecordWord c 0 := by
    change memLoad (UInt256.ofNat (constructorRecordBase c) + ⟨0⟩) mem = _ at h0
    simpa only [u256_add_zero] using h0
  have hr1 := h1.scalar (j := 1) (by decide) hsize
  have hr2 := h2.scalar (j := 2) (by decide) hsize
  have hr3 := h3.scalar (j := 3) (by decide) hsize
  have hr4 := h4.scalar (j := 4) (by decide) hsize
  have hr5 := h5.scalar (j := 13) (by decide) hsize
  simp only [Nat.reduceMul] at hr1 hr2 hr3 hr4 hr5
  have hw (mem : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 mem off 32 = writeWord mem off word := rfl
  unfold cometWithExtendedAssetListCreation_block_902_memory
  simp (disch := decide) only [UInt256.toNat_ofNat_of_lt, hw,
    hr0, ha 0 (by decide), hr1, ha 1 (by decide), hr2, ha 2 (by decide), hr3, ha 3 (by decide),
    hr4, u256_land_comm (constructorRecordWord c 4), ha 4 (by decide), hr5, hf]
  rfl

end Benchmarks.CompoundIII.Comet
