import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.AssetReturn
import Benchmarks.CompoundIII.Comet.AbiRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_031
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_019

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def GetAssetInfoResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 36 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
      (calldataWord I.calldata 4).toNat < 256 then
    ∃ (evm' : EVM.State) (σ' : AccountMap) (z : Bool) (out : ByteArray),
      callViaEVM s0 v.assetList 0 (assetPayload (calldataWord I.calldata 4))
        (z, evm', out) false ∧ σ' = evm'.accountMap ∧ out.size < 2^138 ∧
      if z = true ∧ AssetValid out then
        RDret (deployedRuntime v) g s0 σ' (wordBytes (assetWords out))
      else RDrev (deployedRuntime v) g s0
  else RDrev (deployedRuntime v) g s0

theorem getAssetInfoX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 57)) :
    GetAssetInfoResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachGetAssetInfoBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_871 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_5793_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2^255 + 4
      · have rd3 := cometWithExtendedAssetList_block_5800_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_5812
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < 256
        · obtain ⟨k5, C5, rd5⟩ := cometValidate8_ok (v := v)
            (ret := UInt256.ofNat 5829) (by change 7 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have rd6 := cometWithExtendedAssetList_block_5829
            (immWords := wordsOf (immStore v)) (by change 4 ≤ 1024; decide)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd5
          change RD _ _ _ _ _ (calldataWord I.calldata 4 :: UInt256.ofNat 3164 ::
            UInt256.ofNat 2570 :: []) _ _ _ _ _ _ at rd6
          obtain ⟨evm', σ', z, out, hcall, hs', hout, hf⟩ := cometAssetInternal (v := v)
            (by change 14 ≤ 1024; decide) hc solcFreePtrMem_mload64 (by decide)
            (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest)
            SourceState.init rd6
          unfold GetAssetInfoResult
          rw [if_pos ⟨hv, hlo, hhi, hc⟩]
          refine ⟨evm', σ', z, out, hcall, hs'.accounts, hout, ?_⟩
          by_cases hvalid : z = true ∧ AssetValid out
          · rw [if_pos hvalid] at hf ⊢
            obtain ⟨aw7, k7, C7, rd7⟩ := hf
            exact cometGetAssetInfoReturn (v := v) hvalid.2
              (lt_trans hout (by change 2^138 < 2^256; decide)) rd7
          · rw [if_neg hvalid] at hf ⊢
            exact hf
        · simp only [GetAssetInfoResult, hc, and_false, if_false]
          exact cometValidate8_bad (v := v) (by change 7 ≤ 1024; decide) hc rd4
      · simp only [GetAssetInfoResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_5800_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [GetAssetInfoResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_5800_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [GetAssetInfoResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_5793_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
