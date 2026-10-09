import Benchmarks.CompoundIII.Comet.WithdrawDispatch
import Benchmarks.CompoundIII.Comet.WithdrawInternalEvm
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_035
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_036

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem cometWithdrawCall {v : CometWithExtendedAssetListImmutables}
    {ee : ExecutionEnv} {g : Sat256} {s0 evm : State} {rdata : ByteArray}
    {aw : UInt256} {σ : AccountMap} {k C : Nat} (asset : AccountAddress)
    (hs : SourceState s0 ee σ evm)
    (h : RD (deployedRuntime v) ee g s0 ⟨6901⟩ [EVM.word asset.val, ⟨2308⟩]
      solcFreePtrMem aw rdata σ k C) :
    ∃ result, WithdrawInternalTrace v ee.source ee.source ee.source asset
      (calldataWord ee.calldata 36) evm result ∧ voidOutcomeRun (deployedRuntime v) g s0 result := by
  have r1 := cometWithExtendedAssetList_block_6901 (immWords := wordsOf (immStore v))
    (by change 4 ≤ 1024; decide)
    (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) h
  apply cometWithdrawInternalStart (v := v) ee.source ee.source ee.source asset
    (by change 8 ≤ 1024; decide) hs
    (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) ?_ r1
  intro evm' σ' aw' k' C' hs' hp r2
  have r3 := cometWithExtendedAssetList_block_6909 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) r2
  apply cometWithdrawInternalAfter (v := v) ee.source ee.source ee.source asset
    (free := ⟨128⟩) (by decide) hp ?_ (by decide) ?_ ?_ hs' r3
  · exact (reentrancyMemory_free v _ (by rw [solcFreePtrMem_size])).trans solcFreePtrMem_mload64
  · rw [reentrancyMemory_size v _ (by rw [solcFreePtrMem_size]; decide), solcFreePtrMem_size]
  · have := v.numAssets_lt
    change 128 + 672 + 1696 * v.numAssets.toNat < 2^64
    omega

def WithdrawResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 68 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus then
    ∃ result, WithdrawInternalTrace v I.source I.source I.source
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (calldataWord I.calldata 36) s0 result ∧ voidOutcomeRun (deployedRuntime v) g s0 result
  else RDrev (deployedRuntime v) g s0

theorem withdrawX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 67)) :
    WithdrawResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachWithdrawBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_778 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_6868_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2^255 + 4
      · have rd3 := cometWithExtendedAssetList_block_6875_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 64) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_6887
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨_, _, rd5⟩ := cometValidateAddress_ok (v := v) (ret := UInt256.ofNat 6901)
            (by change 7 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          unfold WithdrawResult
          rw [if_pos ⟨hv, hlo, hhi, hc⟩]
          change RD _ _ _ _ _ [calldataWord I.calldata 4, UInt256.ofNat 2308] _ _ _ _ _ _ at rd5
          rw [← addressWord_eq_ofNat_address hc] at rd5
          exact cometWithdrawCall _ SourceState.init rd5
        · simp only [WithdrawResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 7 ≤ 1024; decide) hc rd4
      · simp only [WithdrawResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_6875_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 64) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [WithdrawResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_6875_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 64) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [WithdrawResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_6868_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
