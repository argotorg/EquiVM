import Benchmarks.CompoundIII.Comet.BaseReward
import Benchmarks.CompoundIII.Comet.CheckedDivEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_055

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometBaseReward {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {principal delta ret : UInt256} {R : List UInt256}
    (hstack : R.length + 9 ≤ 1024) (hp : principal.toNat < 2^104) (hd : delta.toNat < 2^64)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7799⟩
      (principal :: delta :: ⟨11822⟩ :: ⟨11861⟩ :: ⟨8229⟩ :: ret :: R) mem aw rdata σ k C) :
    if BaseRewardValid v principal delta then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (baseRewardWord v principal delta :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  obtain ⟨k1, C1, r1⟩ := cometCheckedMul (v := v)
    (by simp only [List.length_cons]; omega) (baseRewardProduct_lt hp hd)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
  have r2 := cometWithExtendedAssetList_block_11822 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
  simp only [cometWithExtendedAssetList_block_11822_stack,
    wordsOf_immStore_trackingIndexScale, wordOfInt_ofNat_toNat] at r2
  have hdiv1 := cometCheckedDiv (v := v) (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
  by_cases hscale : v.trackingIndexScale ≠ ⟨0⟩
  · rw [if_pos hscale] at hdiv1
    obtain ⟨k3, C3, r3⟩ := hdiv1
    have r4 := cometWithExtendedAssetList_block_11861 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    simp only [cometWithExtendedAssetList_block_11861_stack,
      wordsOf_immStore_accrualDescaleFactor, wordOfInt_ofNat_toNat] at r4
    have hdiv2 := cometCheckedDiv (v := v) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
    by_cases hfactor : v.accrualDescaleFactor ≠ ⟨0⟩
    · rw [if_pos hfactor] at hdiv2
      obtain ⟨k5, C5, r5⟩ := hdiv2
      have r6 := cometWithExtendedAssetList_block_8229 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
      by_cases hfit : (baseRewardWord v principal delta).toNat < 2^64
      · rw [if_pos (show BaseRewardValid v principal delta from ⟨hscale, hfactor, hfit⟩)]
        exact cometSafe64 (v := v) (by omega) hfit hvalid r6
      · rw [if_neg (show ¬ BaseRewardValid v principal delta from fun h ↦ hfit h.2.2)]
        exact cometSafe64_revert (v := v) (by simp only [List.length_cons]; omega) hfit r6
    · rw [if_neg hfactor] at hdiv2
      rw [if_neg (show ¬ BaseRewardValid v principal delta from fun h ↦ hfactor h.2.1)]
      exact hdiv2
  · rw [if_neg hscale] at hdiv1
    rw [if_neg (show ¬ BaseRewardValid v principal delta from fun h ↦ hscale h.1)]
    exact hdiv1

end Benchmarks.CompoundIII.Comet
