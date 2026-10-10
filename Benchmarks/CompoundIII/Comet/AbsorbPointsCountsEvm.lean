import Benchmarks.CompoundIII.Comet.CheckedIncrement32Evm
import Benchmarks.CompoundIII.Comet.AbsorbPointsModel
import Benchmarks.CompoundIII.Comet.LiquidatorPointsMemory
import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbPointsCounts {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ptr n gasUsed absorber ret : UInt256} {σ : AccountMap} {k C : Nat}
    {p : LiquidatorPointsData} {R : List UInt256}
    (hstack : R.length + 18 ≤ 1024) (hm : LiquidatorPointsMemory mem ptr p)
    (ha : p.absorbs.toNat < 2^32) (hb : p.absorbed.toNat < 2^64) (hn : n.toNat < 2^64)
    (h : RD (deployedRuntime v) ee g s0 ⟨16758⟩
      (ptr :: ⟨16794⟩ :: ⟨16812⟩ :: gasUsed :: ⟨13846⟩ :: ⟨16819⟩ :: ⟨16850⟩ ::
        absorber :: ⟨16857⟩ :: n :: ⟨3121⟩ :: ret :: R) mem aw rdata σ k C) :
    if p.absorbs.toNat + 1 < 2^32 ∧ p.absorbed.toNat + n.toNat < 2^64 then
      ∃ mem' aw' k' C', LiquidatorPointsMemory mem' ptr (absorbPointsCounts p n) ∧
        RD (deployedRuntime v) ee g s0 ⟨16812⟩
          (gasUsed :: ⟨13846⟩ :: ⟨16819⟩ :: ⟨16850⟩ :: absorber :: ⟨16857⟩ :: ptr ::
            ⟨3121⟩ :: ret :: R) mem' aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  have hmask : UInt256.land (UInt256.ofNat 4294967295) p.absorbs = p.absorbs := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (bits := 32) rfl ha
  have r1 := cometWithExtendedAssetList_block_16758
    (immWords := wordsOf (immStore v)) (by change R.length + 2 + 15 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  simp only [cometWithExtendedAssetList_block_16758_stack, hm.absorbs, hmask] at r1
  have r2 := cometWithExtendedAssetList_block_16779
    (immWords := wordsOf (immStore v)) (by change R.length + 15 + 1 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  have hr := cometCheckedIncrement32 (v := v) (by change R.length + 13 + 5 ≤ 1024; omega) ha
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  by_cases hi : p.absorbs.toNat + 1 < 2^32
  · rw [if_pos hi] at hr
    obtain ⟨k3, C3, r3⟩ := hr
    have hi' : (p.absorbs + (⟨1⟩ : UInt256)).toNat < 2^32 := by
      change (UInt256.add p.absorbs ⟨1⟩).toNat < 2^32
      rw [addWord_toNat _ _ (by change p.absorbs.toNat + 1 < 2^256; omega)]
      exact hi
    have hmask' : UInt256.land (UInt256.ofNat 4294967295) (p.absorbs + ⟨1⟩) = p.absorbs + ⟨1⟩ := by
      rw [u256_land_comm]
      exact u256LandMaskCleanOfToNat _ _ (bits := 32) rfl hi'
    have r4 := cometWithExtendedAssetList_block_16784
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 13 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    simp only [cometWithExtendedAssetList_block_16784_memory, hmask'] at r4
    have hm4 := hm.writeField 0 (p.absorbs + ⟨1⟩)
    simp only [show (0 : Fin 4).val = 0 from rfl, Nat.mul_zero,
      show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, uint256_add_zero_right] at hm4
    have hload : memLoad (ptr + UInt256.ofNat 32)
        ((p.absorbs + (⟨1⟩ : UInt256)).toByteArray.write 0 mem ptr.toNat 32) = p.absorbed :=
      hm4.absorbed
    have r5 := cometWithExtendedAssetList_block_8229
      (immWords := wordsOf (immStore v)) (by change R.length + 12 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
    obtain ⟨k6, C6, r6⟩ := cometSafe64 (v := v)
      (by change R.length + 10 + 5 ≤ 1024; omega) hn
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r5
    have r7 := cometWithExtendedAssetList_block_16794
      (immWords := wordsOf (immStore v)) (by change R.length + 2 + 14 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
    simp only [cometWithExtendedAssetList_block_16794_stack, hload] at r7
    have r8 := cometWithExtendedAssetList_block_2959
      (immWords := wordsOf (immStore v)) (by change R.length + 13 + 5 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r7
    simp only [cometWithExtendedAssetList_block_2959_stack,
      mask64Clean _ hb] at r8
    have r9 := cometWithExtendedAssetList_block_8244
      (immWords := wordsOf (immStore v)) (by change R.length + 14 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
    by_cases hj : p.absorbed.toNat + n.toNat < 2^64
    · rw [if_pos ⟨hi, hj⟩]
      obtain ⟨k10, C10, r10⟩ := cometCheckedAdd64 (v := v)
        (by change R.length + 11 + 6 ≤ 1024; omega) hb hn hj
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r9
      have hj' : (p.absorbed + n).toNat < 2^64 := by
        change (UInt256.add p.absorbed n).toNat < 2^64
        rw [addWord_toNat _ _ (lt_trans hj (by decide))]
        exact hj
      have r11 := cometWithExtendedAssetList_block_11918
        (immWords := wordsOf (immStore v)) (by change R.length + 9 + 6 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r10
      simp only [cometWithExtendedAssetList_block_11918_memory, mask64Clean _ hj'] at r11
      exact ⟨_, _, _, _, hm4.writeField 1 (p.absorbed + n), r11⟩
    · rw [if_neg (fun hh ↦ hj hh.2)]
      exact cometCheckedAdd64_revert (v := v)
        (by change R.length + 12 + 5 ≤ 1024; omega) hb hn (le_of_not_gt hj) r9
  · rw [if_neg (fun hh ↦ hi hh.1)]
    rwa [if_neg hi] at hr

end Benchmarks.CompoundIII.Comet
