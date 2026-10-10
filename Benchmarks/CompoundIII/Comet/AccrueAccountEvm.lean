import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.AccrueAccountInternal
import Benchmarks.CompoundIII.Comet.AccrueInternalEvm
import Benchmarks.CompoundIII.Comet.AbiRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometAccrueAccountCall {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} (addr : AccountAddress)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨5305⟩ [EVM.word addr.val, ⟨22⟩]
      solcFreePtrMem aw rdata σ k C) :
    voidOutcomeRun (deployedRuntime v) g s0 (accrueAccountOutcome v evm addr) := by
  have r1 := cometWithExtendedAssetList_block_5305 (immWords := wordsOf (immStore v))
    (by change 4 ≤ 1024; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  have hr := cometAccrueInternal (v := v) (by change 39 ≤ 1024; decide) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) r1
  cases hx : accrueOutcome v evm with
  | ok evm' =>
      rw [hx] at hr
      obtain ⟨σ', k', C', hs', hr⟩ := hr
      simp only [accrueAccountOutcome, hx]
      exact cometAccrueAccountUpdate addr hs' hr
  | reverted => simpa only [accrueAccountOutcome, hx, voidOutcomeRun, internalRun] using hr
  | staticViolation =>
      simpa only [accrueAccountOutcome, hx, voidOutcomeRun, internalRun] using hr

def AccrueAccountResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 36 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus then
    voidOutcomeRun (deployedRuntime v) g s0
      (accrueAccountOutcome v s0 (AccountAddress.ofNat (calldataWord I.calldata 4).toNat))
  else RDrev (deployedRuntime v) g s0

theorem accrueAccountX {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 52)) :
    AccrueAccountResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachAccrueAccountBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_925 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_5272_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2^255 + 4
      · have rd3 := cometWithExtendedAssetList_block_5279_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_5291
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k5, C5, rd5⟩ := cometValidateAddress_ok (v := v)
            (ret := UInt256.ofNat 5305) (by change 7 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          unfold AccrueAccountResult
          rw [if_pos ⟨hv, hlo, hhi, hc⟩]
          change RD _ _ _ _ _ [calldataWord I.calldata 4, UInt256.ofNat 22] _ _ _ _ _ _ at rd5
          rw [← addressWord_eq_ofNat_address hc] at rd5
          exact cometAccrueAccountCall _ SourceState.init rd5
        · simp only [AccrueAccountResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 7 ≤ 1024; decide) hc rd4
      · simp only [AccrueAccountResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_5279_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [AccrueAccountResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_5279_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [AccrueAccountResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_5272_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
