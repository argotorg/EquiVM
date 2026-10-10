import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.QuoteInternal
import Benchmarks.CompoundIII.Comet.FreeWordReturn
import Benchmarks.CompoundIII.Comet.AbiRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_009
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def QuoteCollateralResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 68 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus then
    ∃ result, QuoteTrace v (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (calldataWord I.calldata 36) s0 result ∧ match result with
      | none => RDrev (deployedRuntime v) g s0
      | some (evm', value) => RDret (deployedRuntime v) g s0 evm'.accountMap value.toByteArray
  else RDrev (deployedRuntime v) g s0

theorem quoteCollateralX {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 32)) :
    QuoteCollateralResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachQuoteCollateralBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1096 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_4099_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2^255 + 4
      · have rd3 := cometWithExtendedAssetList_block_4106_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 64) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_4118
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k5, C5, rd5⟩ := cometValidateAddress_ok (v := v)
            (ret := UInt256.ofNat 4134) (by change 8 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have rd6 := cometWithExtendedAssetList_block_4134
            (immWords := wordsOf (immStore v)) (by change 5 ≤ 1024; decide)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd5
          change RD _ _ _ _ _ [calldataWord I.calldata 4, calldataWord I.calldata 36,
            UInt256.ofNat 1504, UInt256.ofNat 32] _ _ _ _ _ _ at rd6
          rw [← addressWord_eq_ofNat_address hc] at rd6
          obtain ⟨result, hsearch, hr⟩ := cometQuoteInternal (v := v)
            (by change 23 ≤ 1024; decide) solcFreePtrMem_mload64 (by decide)
            (by have := v.numAssets_lt; change 128 + 832 + 768 * v.numAssets.toNat < 2^64; omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) SourceState.init rd6
          unfold QuoteCollateralResult
          rw [if_pos ⟨hv, hlo, hhi, hc⟩]
          refine ⟨result, hsearch, ?_⟩
          cases result with
          | none => exact hr
          | some result =>
              obtain ⟨evm', value⟩ := result
              obtain ⟨σ', mem, aw, rdata, k7, C7, hs', rd7⟩ := hr
              have hr := cometReturnWord (v := v) (by decide) rd7
              simpa only [hs'.accounts] using hr
        · simp only [QuoteCollateralResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 8 ≤ 1024; decide) hc rd4
      · simp only [QuoteCollateralResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_4106_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 64) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [QuoteCollateralResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_4106_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 64) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [QuoteCollateralResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_4099_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
