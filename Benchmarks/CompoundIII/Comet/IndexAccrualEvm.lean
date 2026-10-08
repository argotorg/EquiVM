import Benchmarks.CompoundIII.Comet.IndexAccrual

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

theorem cometIndexAccrual {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {index rate elapsed ret : UInt256} {R : List UInt256}
    (hstack : R.length + 10 ≤ 1024)
    (hi : index.toNat < 2^64) (hr : rate.toNat < 2^64) (ht : elapsed.toNat < 2^40)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7799⟩
      (rate :: elapsed :: ⟨8559⟩ :: ⟨8565⟩ :: ⟨1000000000000000000⟩ ::
        ⟨8571⟩ :: index :: ret :: R) mem aw rdata σ k C) :
    if IndexAccrualValid index rate elapsed then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (accruedIndexWord index rate elapsed :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, r1⟩ := cometCheckedMul (v := v) (by simpa using hstack)
    (lt_trans (rateTimeProduct_lt hr ht) (by decide))
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_8559
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  obtain ⟨k3, C3, r3⟩ := cometCheckedMul (v := v) (by simp only [List.length_cons]; omega)
    (indexFactorProduct_lt hi hr ht)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  have r4 := cometWithExtendedAssetList_block_8565
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
  change RD _ _ _ _ _ (indexIncrement index rate elapsed :: ⟨8571⟩ :: index :: ret :: R)
    _ _ _ _ _ _ at r4
  by_cases hs : (indexIncrement index rate elapsed).toNat < 2^64
  · obtain ⟨k5, C5, r5⟩ := cometSafe64 (v := v) (by simp only [List.length_cons]; omega)
      hs (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
    have r6 := cometWithExtendedAssetList_block_8571
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
    by_cases ha : index.toNat + (indexIncrement index rate elapsed).toNat < 2^64
    · simp only [IndexAccrualValid, hs, ha, and_self, if_true]
      exact cometCheckedAdd64 (v := v) (by omega) hi hs ha hvalid r6
    · simp only [IndexAccrualValid, ha, and_false, if_false]
      exact cometCheckedAdd64_revert (v := v) (by simp only [List.length_cons]; omega)
        hi hs (Nat.le_of_not_gt ha) r6
  · simp only [IndexAccrualValid, hs, false_and, if_false]
    exact cometSafe64_revert (v := v) (by simp only [List.length_cons]; omega) hs r4

end Benchmarks.CompoundIII.Comet
