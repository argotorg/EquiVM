import Benchmarks.CompoundIII.Comet.ConstructorAllocate

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open cometWithExtendedAssetListCreationBlocks

namespace Benchmarks.CompoundIII.Comet

theorem cometCreationReadAddress {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr w ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hread : memLoad ptr mem = w) (hcanon : w.toNat < 2^160)
    (hret : (D_J cometWithExtendedAssetListCreationBytecode 0).contains ret = true)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2747⟩
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ret
      (w :: R) mem aw' rdata σ k' C' := by
  have hclean := u256LandMaskCleanOfToNat (bits := 160) w
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
    (by native_decide) hcanon
  have r1 := cometWithExtendedAssetListCreation_block_2747_fallthrough hstack (by
    rw [hread, hclean, u256_sub_self]; rfl) h
  have r2 := cometWithExtendedAssetListCreation_block_2767
    (by change R.length + 1 + 1 ≤ 1024; omega) hret r1
  simp only [cometWithExtendedAssetListCreation_block_2767_stack, hread] at r2
  exact ⟨_, _, _, r2⟩

theorem cometCreationReadUint64 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr w ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hread : memLoad ptr mem = w) (hcanon : w.toNat < 2^64)
    (hret : (D_J cometWithExtendedAssetListCreationBytecode 0).contains ret = true)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2768⟩
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ret
      (w :: R) mem aw' rdata σ k' C' := by
  have hclean := u256LandMaskCleanOfToNat (bits := 64) w
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))
    (by native_decide) hcanon
  have r1 := cometWithExtendedAssetListCreation_block_2768_fallthrough hstack (by
    rw [hread, hclean, u256_sub_self]; rfl) h
  have r2 := cometWithExtendedAssetListCreation_block_2788
    (by change R.length + 1 + 1 ≤ 1024; omega) hret r1
  simp only [cometWithExtendedAssetListCreation_block_2788_stack, hread] at r2
  exact ⟨_, _, _, r2⟩

theorem cometCreationReadUint104 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr w ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hread : memLoad ptr mem = w) (hcanon : w.toNat < 2^104)
    (hret : (D_J cometWithExtendedAssetListCreationBytecode 0).contains ret = true)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2789⟩
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ret
      (w :: R) mem aw' rdata σ k' C' := by
  have hclean := u256LandMaskCleanOfToNat (bits := 104) w
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 104)) (UInt256.ofNat 1))
    (by native_decide) hcanon
  have r1 := cometWithExtendedAssetListCreation_block_2789_fallthrough hstack (by
    rw [hread, hclean, u256_sub_self]; rfl) h
  have r2 := cometWithExtendedAssetListCreation_block_2809
    (by change R.length + 1 + 1 ≤ 1024; omega) hret r1
  simp only [cometWithExtendedAssetListCreation_block_2809_stack, hread] at r2
  exact ⟨_, _, _, r2⟩

theorem cometCreationReadUint8 {tail : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr w ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 4 ≤ 1024)
    (hread : memLoad ptr mem = w) (hcanon : w.toNat < 2^8)
    (hret : (D_J cometWithExtendedAssetListCreationBytecode 0).contains ret = true)
    (h : RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ⟨2810⟩
      (ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (cometWithExtendedAssetListCreationBytecode ++ tail) ee g s0 ret
      (w :: R) mem aw' rdata σ k' C' := by
  have hclean := u256LandMaskCleanOfToNat (bits := 8) w
    (UInt256.ofNat 255) (by native_decide) hcanon
  have r1 := cometWithExtendedAssetListCreation_block_2810_fallthrough hstack (by
    rw [hread, hclean, u256_sub_self]; rfl) h
  have r2 := cometWithExtendedAssetListCreation_block_2824
    (by change R.length + 1 + 1 ≤ 1024; omega) hret r1
  simp only [cometWithExtendedAssetListCreation_block_2824_stack, hread] at r2
  exact ⟨_, _, _, r2⟩

end Benchmarks.CompoundIII.Comet
