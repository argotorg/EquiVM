import Benchmarks.CompoundIII.Comet.ConstructorScaleWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

def constructorScaleMemory (c : ConstructorConfig) (w : UInt256) (mem : ByteArray) : ByteArray :=
  writeWord (writeWord mem 576 (constructorScaleWord w)) 608 (constructorRecordWord c 14)

theorem constructorScaleMemory_data {c : ConstructorConfig} {mem : ByteArray}
    (hm : ConstructorDataMemory c mem) (w : UInt256) :
    ConstructorDataMemory c (constructorScaleMemory c w mem) := by
  have hb : 928 ≤ constructorRecordBase c := by unfold constructorRecordBase; omega
  exact (hm.writeBelow _ (by omega)).writeBelow _ (by omega)

theorem constructorScaleMemory_eq {c : ConstructorConfig} {w : UInt256} {mem : ByteArray}
    (hw : w.toNat ≤ 18) (hm : ConstructorDataMemory c mem)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size) :
    cometWithExtendedAssetListCreation_block_988_fallthrough_memory (mem := mem)
      (x0 := UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
      (x1 := ⟨255⟩) (x2 := w) (x3 := UInt256.ofNat (constructorRecordBase c)) =
      constructorScaleMemory c w mem := by
  have hm' := hm.writeBelow (constructorScaleWord w) (off := 576)
    (by unfold constructorRecordBase; omega)
  have hr := hm'.scalar (j := 14) (by decide) hsize
  simp only [Nat.reduceMul] at hr
  have ht : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
      (constructorRecordWord c 14) = constructorRecordWord c 14 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 64) _ _ (by native_decide)
      (constructorRecordWord_uint64Canonical c (by decide) (by decide))
  have hwrite (mem : ByteArray) (off : Nat) (word : UInt256) :
      word.toByteArray.write 0 mem off 32 = writeWord mem off word := rfl
  have hbyte : (⟨255⟩ : UInt256) = UInt256.ofNat 255 := rfl
  unfold cometWithExtendedAssetListCreation_block_988_fallthrough_memory
  simp (disch := decide) only [UInt256.toNat_ofNat_of_lt, hwrite, hbyte,
    constructorScale_clean hw, hr, ht]
  rfl

theorem cometConstructorScale {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {σ : AccountMap} {c : ConstructorConfig} {mem rdata : ByteArray}
    {w aw : UInt256} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 5 ≤ 1024) (hw : w.toNat ≤ 18) (hm : ConstructorDataMemory c mem)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨988⟩
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1) ::
        ⟨255⟩ :: w :: UInt256.ofNat (constructorRecordBase c) :: R) mem aw rdata σ k C) :
    if 6 ≤ w.toNat then
      ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1024⟩
        (UInt256.ofNat (constructorRecordBase c) :: R) (constructorScaleMemory c w mem)
        aw' rdata σ k' C'
    else RDrev (cometWithExtendedAssetListCreationBytecode ++ tail) g s0 := by
  have hbyte : (⟨255⟩ : UInt256) = UInt256.ofNat 255 := rfl
  split
  · rename_i hlo
    obtain ⟨aw', k', C', r⟩ := cometWithExtendedAssetListCreation_block_988_fallthrough_packed
      hstack (by
      rw [hbyte, constructorScale_clean hw]
      apply ugt_zero
      rw [constructorScaleWord_toNat hw]
      exact (constructorScale_min hw).mpr hlo) h
    exact ⟨aw', k', C', by simpa only [constructorScaleMemory_eq hw hm hsize] using r⟩
  · rename_i hlo
    have r := cometWithExtendedAssetListCreation_block_988_taken hstack (by
      rw [hbyte, constructorScale_clean hw, ugt_one (by
        rw [constructorScaleWord_toNat hw]
        have hh := (constructorScale_min hw).not.mpr hlo
        change _ < 1000000
        omega)]
      decide) (by native_decide) h
    exact cometWithExtendedAssetListCreation_block_2285 (by
      change R.length + 1 + 3 ≤ 1024
      omega) r

end Benchmarks.CompoundIII.Comet
