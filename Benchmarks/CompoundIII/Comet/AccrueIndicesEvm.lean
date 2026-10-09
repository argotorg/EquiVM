import Benchmarks.CompoundIII.Comet.AccrueRewardsEvm
import Benchmarks.CompoundIII.Comet.AccruedIndicesEvm
import Benchmarks.CompoundIII.Comet.AccrueStatic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAccrueIndicesWrite {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {supply borrow ret : UInt256} {R : List UInt256}
    (hstack : R.length + 8 ≤ 1024) (hperm : ee.perm = true) (hs : SourceState s0 ee σ evm)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7962⟩ (borrow :: supply :: ret :: R)
      mem aw rdata σ k C) :
    ∃ σ' k' C', SourceState s0 ee σ'
      (storeTotalsIndex (storeTotalsIndex evm true borrow) false supply) ∧
      RD (deployedRuntime v) ee g s0 ret (⟨0⟩ :: R) mem aw rdata σ' k' C' := by
  obtain ⟨k1, C1, r1⟩ := cometWithExtendedAssetList_block_7962
    (immWords := wordsOf (immStore v)) hstack hperm hvalid h
  have hlo (old : UInt256) :
      UInt256.lor
        (UInt256.land supply (UInt256.sub
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))
        (UInt256.land (UInt256.lnot (UInt256.sub
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1))) old) =
      uint64FieldWrite old supply 0 := (uint64FieldWrite_zero old supply).symm
  rw [hlo] at r1
  have hs1 := sourceState_storeTotalsIndex hs true borrow
  have hs2 := sourceState_storeTotalsIndex hs1 false supply
  exact ⟨_, k1, C1, hs2, r1⟩

theorem cometAccrueThen {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {mem rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} {elapsed time ret : UInt256} {R : List UInt256}
    (hstack : R.length + 37 ≤ 1024) (ht : elapsed.toNat < 2^40) (hs : SourceState s0 ee σ evm)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (h : RD (deployedRuntime v) ee g s0 ⟨7946⟩ (time :: elapsed :: ret :: R)
      mem aw rdata σ k C) :
    internalRun (deployedRuntime v) ee g s0 mem aw rdata ret R
      (accrueThenOutcome v evm elapsed time) := by
  have r1 := cometWithExtendedAssetList_block_7946 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hindices := cometAccruedIndices (v := v)
    (by simpa only [List.length_cons] using hstack) ht
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  dsimp only at hindices
  have hr0 := hs.storageRead ⟨0⟩
  have hr1 := hs.storageRead ⟨1⟩
  by_cases hv : AccrueIndicesValid v evm elapsed
  · have hv' : AccruedIndicesValid v (solcSlotWordAt ⟨0⟩ σ ee)
        (solcSlotWordAt ⟨1⟩ σ ee) elapsed := by
      simpa only [AccrueIndicesValid, hr0, hr1] using hv
    rw [if_pos hv'] at hindices
    obtain ⟨k2, C2, r2⟩ := hindices
    by_cases hperm : ee.perm = true
    · obtain ⟨σ3, k3, C3, hs3, r3⟩ := cometAccrueIndicesWrite (v := v)
        (by simp only [List.length_cons]; omega) hperm hs
        (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r2
      have hs3' : SourceState s0 ee σ3 (accrueIndicesState evm v elapsed) := by
        simpa only [accrueIndicesState, hr0, hr1] using hs3
      simp only [accrueThenOutcome, if_pos hv, hs.env, hperm, if_true]
      exact cometAccrueRewards (v := v) (by omega) hperm hs3' hvalid r3
    · have hp : ee.perm = false := Bool.eq_false_iff.mpr hperm
      simp only [accrueThenOutcome, if_pos hv, hs.env, hp, Bool.false_eq_true, if_false]
      exact cometAccrueStatic (v := v) (by simp only [List.length_cons]; omega) hp r2
  · have hv' : ¬ AccruedIndicesValid v (solcSlotWordAt ⟨0⟩ σ ee)
        (solcSlotWordAt ⟨1⟩ σ ee) elapsed := by
      simpa only [AccrueIndicesValid, hr0, hr1] using hv
    rw [if_neg hv'] at hindices
    simp only [accrueThenOutcome, if_neg hv]
    exact hindices

end Benchmarks.CompoundIII.Comet
