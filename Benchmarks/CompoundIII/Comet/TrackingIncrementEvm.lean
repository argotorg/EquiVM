import Benchmarks.CompoundIII.Comet.TrackingAccrualModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometTrackingIncrement {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {total elapsed ret : UInt256}
    {borrow : Bool} {R : List UInt256} (hstack : R.length + 9 ≤ 1024)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7799⟩
      (trackingSpeed v borrow :: elapsed :: ⟨8224⟩ :: total :: ⟨8229⟩ :: ret :: R)
      mem aw rdata σ k C) :
    if TrackingIncrementValid v borrow total elapsed then
      ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (trackingIncrement v borrow total elapsed :: R) mem aw rdata σ k' C'
    else RDrev (deployedRuntime v) g s0 := by
  by_cases hm : (trackingSpeed v borrow).toNat * elapsed.toNat < UInt256.size
  · obtain ⟨k1, C1, r1⟩ := cometCheckedMul (v := v)
      (by simp only [List.length_cons]; omega) hm
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) h
    have r2 := cometWithExtendedAssetList_block_8224 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r1
    have hd := cometDivBaseWei (v := v) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
    by_cases hv : DivBaseWeiValid v (UInt256.mul (trackingSpeed v borrow) elapsed) total
    · rw [if_pos hv] at hd
      obtain ⟨k3, C3, r3⟩ := hd
      have r4 := cometWithExtendedAssetList_block_8229 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
      by_cases hs : (trackingIncrement v borrow total elapsed).toNat < 2^64
      · rw [if_pos (show TrackingIncrementValid v borrow total elapsed from ⟨hm, hv, hs⟩)]
        exact cometSafe64 (v := v) (by omega) hs hvalid r4
      · rw [if_neg (show ¬ TrackingIncrementValid v borrow total elapsed from
          fun h ↦ hs h.2.2)]
        exact cometSafe64_revert (v := v) (by simp only [List.length_cons]; omega) hs r4
    · rw [if_neg hv] at hd
      rw [if_neg (show ¬ TrackingIncrementValid v borrow total elapsed from
        fun h ↦ hv h.2.1)]
      exact hd
  · rw [if_neg (show ¬ TrackingIncrementValid v borrow total elapsed from fun h ↦ hm h.1)]
    exact cometCheckedMul_revert (v := v) (by simp only [List.length_cons]; omega)
      (le_of_not_gt hm) h

end Benchmarks.CompoundIII.Comet
