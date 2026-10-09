import Benchmarks.CompoundIII.Comet.AbsorbPointsModel
import Benchmarks.CompoundIII.Comet.LiquidatorPointsMemory
import Benchmarks.CompoundIII.Comet.ArithmeticRoutines
import Benchmarks.CompoundIII.Comet.CheckedAdd128Evm
import Benchmarks.CompoundIII.Comet.Safe128Evm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_016
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_064
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_076

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAbsorbPointsSpend {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw ptr gasUsed absorber ret : UInt256} {σ : AccountMap} {k C : Nat}
    {p : LiquidatorPointsData} {R : List UInt256}
    (hstack : R.length + 14 ≤ 1024) (hm : LiquidatorPointsMemory mem ptr p)
    (hp : p.spend.toNat < 2^128)
    (h : RD (deployedRuntime v) ee g s0 ⟨16812⟩
      (gasUsed :: ⟨13846⟩ :: ⟨16819⟩ :: ⟨16850⟩ :: absorber :: ⟨16857⟩ :: ptr ::
        ⟨3121⟩ :: ret :: R) mem aw rdata σ k C) :
    if AbsorbPointsSpendValid p gasUsed (UInt256.ofNat ee.header.baseFeePerGas) then
      ∃ mem' aw' k' C', LiquidatorPointsMemory mem' ptr
          (absorbPointsSpend p gasUsed (UInt256.ofNat ee.header.baseFeePerGas)) ∧
        RD (deployedRuntime v) ee g s0 ⟨16850⟩
          (absorber :: ⟨16857⟩ :: ptr :: ⟨3121⟩ :: ret :: R) mem' aw' rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  let fee := UInt256.ofNat ee.header.baseFeePerGas
  let cost := absorbPointsCost gasUsed fee
  have r1 := cometWithExtendedAssetList_block_16812
    (immWords := wordsOf (immStore v)) (by change R.length + 8 + 3 ≤ 1024; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases hmul : gasUsed.toNat * fee.toNat < UInt256.size
  · obtain ⟨k2, C2, r2⟩ := cometCheckedMul (v := v)
      (by change R.length + 7 + 5 ≤ 1024; omega) hmul
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    have r3 := cometWithExtendedAssetList_block_13846
      (immWords := wordsOf (immStore v)) (by change R.length + 8 + 1 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    obtain ⟨hcost, k4, C4, r4⟩ | ⟨hcost, hr⟩ := cometSafe128 (v := v)
      (by change R.length + 6 + 6 ≤ 1024; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r3
    · have r5 := cometWithExtendedAssetList_block_16819
        (immWords := wordsOf (immStore v)) (by change R.length + 2 + 10 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r4
      simp only [cometWithExtendedAssetList_block_16819_stack, hm.spend] at r5
      have r6 := cometWithExtendedAssetList_block_2451
        (immWords := wordsOf (immStore v)) (by change R.length + 9 + 5 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
      simp only [cometWithExtendedAssetList_block_2451_stack, mask128Clean _ hp] at r6
      have r7 := cometWithExtendedAssetList_block_13899
        (immWords := wordsOf (immStore v)) (by change R.length + 10 + 1 ≤ 1024; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
      obtain ⟨hsum, k8, C8, r8⟩ | ⟨hsum, hr⟩ := cometCheckedAdd128 (v := v)
        (by change R.length + 7 + 6 ≤ 1024; omega) hp hcost
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r7
      · rw [if_pos (show AbsorbPointsSpendValid p gasUsed fee from ⟨hmul, hcost, hsum⟩)]
        have hs : (p.spend + cost).toNat < 2^128 := by
          change (UInt256.add p.spend cost).toNat < 2^128
          rw [addWord_toNat p.spend cost (lt_trans hsum (by decide))]
          exact hsum
        have r9 := cometWithExtendedAssetList_block_16837
          (immWords := wordsOf (immStore v)) (by change R.length + 5 + 6 ≤ 1024; omega)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r8
        have hmask := mask128Clean (p.spend + cost) hs
        simp only [cometWithExtendedAssetList_block_16837_memory] at r9
        change RD _ _ _ _ _ _
          ((UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
              (UInt256.ofNat 1)) (p.spend + cost)).toByteArray.write 0 mem
              (ptr + UInt256.ofNat 64).toNat 32) _ _ _ _ _ at r9
        rw [hmask] at r9
        exact ⟨_, _, _, _, hm.writeField 2 (p.spend + cost), r9⟩
      · rw [if_neg (show ¬ AbsorbPointsSpendValid p gasUsed fee from fun hv ↦ hsum hv.2.2)]
        exact hr
    · rw [if_neg (show ¬ AbsorbPointsSpendValid p gasUsed fee from fun hv ↦ hcost hv.2.1)]
      exact hr
  · rw [if_neg (show ¬ AbsorbPointsSpendValid p gasUsed fee from fun hv ↦ hmul hv.1)]
    exact cometCheckedMul_revert (v := v)
      (by change R.length + 8 + 4 ≤ 1024; omega) (le_of_not_gt hmul) r1

end Benchmarks.CompoundIII.Comet
