import Benchmarks.CompoundIII.Comet.AccrueIndicesEvm
import Benchmarks.CompoundIII.Comet.AccrualTimeEvm

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAccrueInternal {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {ret : UInt256} {R : List UInt256}
    (hstack : R.length + 37 ≤ 1024) (hs : SourceState s0 ee σ evm)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7886⟩ (ret :: R) mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ret R (accrueOutcome v evm) := by
  let time := timestampWord ee
  let w1 := solcSlotWordAt ⟨1⟩ σ ee
  let elapsed := currentElapsed time w1
  have hr1 : Solm.EVM.storageLoad evm ee.codeOwner ⟨1⟩ = w1 := by
    simpa only [hs.env] using hs.storageRead ⟨1⟩
  have he : accrueElapsed evm = elapsed := by
    simp only [accrueElapsed, hs.env, hr1]
    rfl
  have r1 := cometWithExtendedAssetList_block_7886 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  by_cases ht : time.toNat < 2^40
  · obtain ⟨k2, C2, r2⟩ := cometNow (v := v) (by simp only [List.length_cons]; omega) ht
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
    obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_7894
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
    change RD _ _ _ _ _
      (UInt256.land (UInt256.shiftRight w1 ⟨208⟩) ⟨1099511627775⟩ ::
        ⟨7926⟩ :: ⟨7936⟩ :: time :: ret :: R) _ _ _ _ _ _ at r3
    rw [← lastAccrualWord_eq] at r3
    have r4 := cometWithExtendedAssetList_block_7920 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r3
    by_cases hle : (lastAccrualWord w1).toNat ≤ time.toNat
    · have hv : AccrueTimeValid evm := by
        simpa only [AccrueTimeValid, hs.env, hr1] using And.intro ht hle
      obtain ⟨k5, C5, r5⟩ := cometCheckedSub40 (v := v)
        (by simp only [List.length_cons]; omega) ht (lastAccrualWord_lt _) hle
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r4
      have hdt : elapsed.toNat < 2^40 := currentElapsed_lt ht hle
      have r6 := cometWithExtendedAssetList_block_7926 (immWords := wordsOf (immStore v))
        (by simp only [List.length_cons]; omega)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r5
      change RD _ _ _ _ _ (UInt256.land (UInt256.ofNat 1099511627775) elapsed :: time :: ret :: R)
        _ _ _ _ _ _ at r6
      rw [mask40Clean elapsed hdt] at r6
      by_cases hz : elapsed = ⟨0⟩
      · have r7 := cometWithExtendedAssetList_block_7936_fallthrough
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hz r6
        have r8 := cometWithExtendedAssetList_block_7943 (immWords := wordsOf (immStore v))
          (by omega) hvalid r7
        simp only [accrueOutcome, if_pos hv, he, if_pos hz]
        exact ⟨σ, _, _, hs, r8⟩
      · have r7 := cometWithExtendedAssetList_block_7936_taken
          (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hz
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r6
        simp only [accrueOutcome, if_pos hv, he, if_neg hz, hs.env]
        exact cometAccrueThen (v := v) hstack hdt hs hvalid r7
    · have hv : ¬ AccrueTimeValid evm := by
        simpa only [AccrueTimeValid, hs.env, hr1] using
          (show ¬ (time.toNat < 2^40 ∧ (lastAccrualWord w1).toNat ≤ time.toNat) from
            fun h ↦ hle h.2)
      simp only [accrueOutcome, if_neg hv]
      exact cometCheckedSub40_revert (v := v) (by simp only [List.length_cons]; omega)
        ht (lastAccrualWord_lt _) (Nat.lt_of_not_ge hle) r4
  · have hv : ¬ AccrueTimeValid evm := by
      simpa only [AccrueTimeValid, hs.env, hr1] using
        (show ¬ (time.toNat < 2^40 ∧ (lastAccrualWord w1).toNat ≤ time.toNat) from fun h ↦ ht h.1)
    simp only [accrueOutcome, if_neg hv]
    exact cometNow_revert (v := v) (by change R.length + 2 + 3 ≤ 1024; omega) ht r1

end Benchmarks.CompoundIII.Comet
