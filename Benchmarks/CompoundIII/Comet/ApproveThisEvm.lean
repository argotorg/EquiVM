import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.ApproveThisInternal
import Benchmarks.CompoundIII.Comet.TwoAddressUintDecode
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def ApproveThisResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ TwoAddressUintCalldataValid I then
    ∃ result, ApproveThisTrace v
      (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (AccountAddress.ofNat (calldataWord I.calldata 36).toNat)
      (calldataWord I.calldata 68) s0 result ∧ ApproveThisRun v g s0 result
  else RDrev (deployedRuntime v) g s0

theorem approveThisX {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 51)) :
    ApproveThisResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachApproveThisBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_934 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_5107_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    have rd3 := cometWithExtendedAssetList_block_5114
      (immWords := wordsOf (immStore v)) (by decide)
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
    have hd := cometDecodeTwoAddressesUint (v := v) (by decide) hsz hsize
      (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd3
    by_cases hargs : TwoAddressUintCalldataValid I
    · rw [if_pos hargs] at hd
      obtain ⟨k4, C4, rd4⟩ := hd
      rw [← addressWord_eq_ofNat_address hargs.2.2.1,
        ← addressWord_eq_ofNat_address hargs.2.2.2] at rd4
      unfold ApproveThisResult
      rw [if_pos ⟨hv, hargs⟩]
      exact cometApproveThisBody _ _ _ SourceState.init rd4
    · rw [if_neg hargs] at hd
      simpa only [ApproveThisResult, hargs, and_false, if_false] using hd
  · simp only [ApproveThisResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_5107_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
