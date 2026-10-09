import Benchmarks.CompoundIII.Comet.ConstructorRemainingImmsMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def constructorRemainingImmMemory (c : ConstructorConfig) (w : UInt256)
    (mem : ByteArray) : ByteArray :=
  constructorBorrowMemory c (constructorSupplyMemory c (constructorRewardMemory c w mem))

theorem constructorRemainingImmMemory_low {c : ConstructorConfig} {w ptr : UInt256}
    {mem : ByteArray} (hin : ptr.toNat + 32 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ 288) :
    memLoad ptr (constructorRemainingImmMemory c w mem) = memLoad ptr mem := by
  unfold constructorRemainingImmMemory constructorBorrowMemory constructorSupplyMemory
    constructorRewardMemory
  simp (disch := (first | omega | (simp only [writeWord_sparse_size]; omega))) only
    [memLoad_writeWord_preserved]

theorem constructorInitialImmMemory_delegate (c : ConstructorConfig) (w : UInt256)
    (mem : ByteArray) :
    memLoad (UInt256.ofNat 256) (constructorInitialImmMemory c w mem) =
      constructorRecordWord c 4 := by
  unfold constructorInitialImmMemory
  have hn : (UInt256.ofNat 256).toNat = 256 := rfl
  rw [memLoad_writeWord_preserved _ _ _ _ (by simp only [writeWord_sparse_size]; omega)
    (Or.inl (by decide))]
  rw [memLoad_writeWord_preserved _ _ _ _ (by simp only [writeWord_sparse_size]; omega)
    (Or.inl (by decide))]
  exact memLoad_writeWord_self _ (UInt256.ofNat 256) _

theorem constructorScaleMemory_low {c : ConstructorConfig} {w ptr : UInt256} {mem : ByteArray}
    (hin : ptr.toNat + 32 ≤ mem.size) (hptr : ptr.toNat + 32 ≤ 576) :
    memLoad ptr (constructorScaleMemory c w mem) = memLoad ptr mem := by
  unfold constructorScaleMemory
  simp (disch := (first | omega | (simp only [writeWord_sparse_size]; omega))) only
    [memLoad_writeWord_preserved]

theorem constructorInitialImmMemory_free {c : ConstructorConfig} {w : UInt256} {mem : ByteArray}
    (hm : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (constructorInitialImmMemory c w mem) =
      memLoad (UInt256.ofNat 64) mem := by
  unfold constructorInitialImmMemory
  have hn : (UInt256.ofNat 64).toNat = 64 := rfl
  simp (disch := (first | omega | (simp only [writeWord_sparse_size]; omega))) only
    [memLoad_writeWord_preserved]

def constructorFactoryCallMemory (c : ConstructorConfig) (w ptr : UInt256)
    (mem : ByteArray) : ByteArray :=
  writeWord (constructorRemainingImmMemory c w mem) ptr.toNat constructorFactorySelectorWord

theorem constructorScaleInitialMemory_delegate (c : ConstructorConfig) (w : UInt256)
    (mem : ByteArray) :
    memLoad (UInt256.ofNat 256) (constructorScaleMemory c w (constructorInitialImmMemory c w mem)) =
      constructorRecordWord c 4 := by
  rw [constructorScaleMemory_low (by
    unfold constructorInitialImmMemory
    simp only [writeWord_sparse_size]
    change 288 ≤ _
    omega) (by decide)]
  exact constructorInitialImmMemory_delegate c w mem

theorem constructorScaleInitialMemory_free {c : ConstructorConfig} {w : UInt256} {mem : ByteArray}
    (hm : 96 ≤ mem.size) :
    memLoad (UInt256.ofNat 64) (constructorScaleMemory c w (constructorInitialImmMemory c w mem)) =
      memLoad (UInt256.ofNat 64) mem := by
  rw [constructorScaleMemory_low (by
    unfold constructorInitialImmMemory
    simp only [writeWord_sparse_size]
    change 96 ≤ _
    omega) (by decide)]
  exact constructorInitialImmMemory_free hm

theorem cometConstructorRemainingImms {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {σ : AccountMap} {c : ConstructorConfig} {mem rdata : ByteArray}
    {w aw ptr : UInt256} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : ConstructorDataMemory c mem)
    (hscale : memLoad (UInt256.ofNat 576) mem = constructorScaleWord w)
    (hdelegate : memLoad (UInt256.ofNat 256) mem = constructorRecordWord c 4)
    (hptr : memLoad (UInt256.ofNat 64) mem = ptr)
    (hsize : 22161 + 224 * c.assetConfigs.length < UInt256.size)
    (hn : c.assetConfigs.length ≤ 24)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1024⟩
      (UInt256.ofNat (constructorRecordBase c) :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨1291⟩
      ((g.subNat C').toUInt256 :: constructorRecordWord c 4 :: ptr :: UInt256.ofNat 4 :: ptr ::
        UInt256.ofNat 32 :: UInt256.ofNat (constructorRecordBase c) :: ptr :: R)
      (constructorFactoryCallMemory c w ptr mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, r1⟩ := cometWithExtendedAssetListCreation_block_1024_packed (by omega) h
  obtain ⟨hstk1, hmem1⟩ := constructorReward_eq hm hscale hsize R
  rw [hstk1, hmem1] at r1
  have hm1 := constructorRewardMemory_data hm w
  obtain ⟨aw2, k2, C2, r2⟩ := cometWithExtendedAssetListCreation_block_1119_packed (by omega) r1
  obtain ⟨hstk2, hmem2⟩ := constructorSupply_eq hm1 hsize R
  rw [hstk2, hmem2] at r2
  have hm2 := constructorSupplyMemory_data hm1
  have hm288 : 288 ≤ mem.size := by
    have hp := hm.present
    unfold constructorAssetFree constructorArrayEnd constructorArrayBase constructorRecordBase at hp
    omega
  have hd := (constructorRemainingImmMemory_low (c := c) (w := w)
    (ptr := UInt256.ofNat 256) (by change 288 ≤ mem.size; omega) (by decide)).trans hdelegate
  have hf := (constructorRemainingImmMemory_low (c := c) (w := w)
    (ptr := UInt256.ofNat 64) (by change 96 ≤ mem.size; omega) (by decide)).trans hptr
  obtain ⟨aw3, k3, C3, r3⟩ := cometWithExtendedAssetListCreation_block_1200_packed (by omega) r2
  obtain ⟨hstk3, hmem3⟩ := constructorFactorySetup_eq hm2 hsize hn hd hf R
  rw [hstk3, hmem3] at r3
  have r4 := cometWithExtendedAssetListCreation_block_1279 (by
    change R.length + 3 + 7 ≤ 1024
    omega) r3
  have ha : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (constructorRecordWord c 4) = constructorRecordWord c 4 := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat (bits := 160) _ _ (by native_decide)
      (constructorRecordWord_addressCanonical c (by decide))
  refine ⟨aw3, k3 + 9, C3 + 26, ?_⟩
  simpa only [cometWithExtendedAssetListCreation_block_1279_stack, ha, Nat.add_assoc] using r4

end Benchmarks.CompoundIII.Comet
