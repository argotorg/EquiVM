import Benchmarks.CompoundIII.Comet.AccrueInternalModel
import Benchmarks.CompoundIII.Comet.TrackingBranchEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAccrueRewards {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {elapsed time ret : UInt256} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨8033⟩
      (⟨0⟩ :: elapsed :: time :: ⟨3121⟩ :: ret :: R) mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ret R
      (if AccrueRewardsValid v evm elapsed then .ok (accrueRewardsState evm v elapsed time)
      else .reverted) := by
  have hsupply := cometTrackingSupplyBranch (v := v)
    (by simpa only [List.length_cons] using hstack) hperm hs h
  by_cases hsup : TrackingBranchValid v false evm elapsed
  · rw [if_pos hsup] at hsupply
    obtain ⟨σ1, dummy, k1, C1, hs1, r1⟩ := hsupply
    have hborrow := cometTrackingBorrowBranch (v := v)
      (by simp only [List.length_cons]; omega) hperm hs1 r1
    by_cases hbor : TrackingBranchValid v true (trackingBranchState evm v false elapsed) elapsed
    · rw [if_pos hbor] at hborrow
      obtain ⟨σ2, a, b, c, k2, C2, hs2, r2⟩ := hborrow
      obtain ⟨k3, C3, r3⟩ := cometWithExtendedAssetList_block_8126
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) hperm
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
      have hword (old : UInt256) :
          UInt256.lor
            (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208))
              (UInt256.shiftLeft time (UInt256.ofNat 208)))
            (UInt256.land
              (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208)))
              old) = initializeTimeWord old time := by
        unfold initializeTimeWord
        rw [u256_land_comm (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208)),
          u256_land_comm (UInt256.lnot
            (UInt256.shiftLeft (UInt256.ofNat 1099511627775) (UInt256.ofNat 208)))]
      rw [hword] at r3
      have r4 := cometWithExtendedAssetList_block_3121 (immWords := wordsOf (immStore v))
        (by omega) hvalid r3
      rw [if_pos (show AccrueRewardsValid v evm elapsed from ⟨hsup, hbor⟩)]
      exact ⟨_, _, _, sourceState_storeLastAccrual hs2 time, r4⟩
    · rw [if_neg hbor] at hborrow
      rw [if_neg (show ¬ AccrueRewardsValid v evm elapsed from fun h ↦ hbor h.2)]
      exact hborrow
  · rw [if_neg hsup] at hsupply
    rw [if_neg (show ¬ AccrueRewardsValid v evm elapsed from fun h ↦ hsup h.1)]
    exact hsupply

end Benchmarks.CompoundIII.Comet
