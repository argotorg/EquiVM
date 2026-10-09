import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.CollateralCheckExternal
import Benchmarks.CompoundIII.Comet.AbiRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_010
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_018
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_011

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

theorem isLiquidatableX {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 0)) :
    CollateralCheckPublicResult v false I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachIsLiquidatableBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1384 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_1415_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 36 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2^255 + 4
      · have rd3 := cometWithExtendedAssetList_block_1422_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 32) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_1434
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k5, C5, rd5⟩ := cometValidateAddress_ok (v := v)
            (ret := UInt256.ofNat 1450) (by change 8 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have rd6 := cometWithExtendedAssetList_block_1450
            (immWords := wordsOf (immStore v)) (by change 4 ≤ 1024; decide)
            (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd5
          change RD _ _ _ _ (collateralCheckPc false)
            [calldataWord I.calldata 4, UInt256.ofNat 1455, UInt256.ofNat 32]
            _ _ _ _ _ _ at rd6
          rw [← addressWord_eq_ofNat_address hc] at rd6
          obtain ⟨result, ht, hr⟩ := cometCollateralCheck (v := v) false
            (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
            (by change 36 ≤ 1024; decide) solcFreePtrMem_mload64 (by decide)
            (by rw [solcFreePtrMem_size])
            (by rw [solcFreePtrMem_size]; decide)
            (by have := v.numAssets_lt
                change 128 + 160 + 928 * v.numAssets.toNat + 256 < 2^64
                omega)
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest)
            SourceState.init rd6
          unfold CollateralCheckPublicResult
          rw [if_pos ⟨hv, hlo, hhi, hc⟩]
          refine ⟨result, ht, ?_⟩
          cases result with
          | none => exact hr
          | some result =>
              obtain ⟨evm', value⟩ := result
              obtain ⟨σ', mem, free, aw, data, k7, C7, hs', _, _, _, _, _, rd7⟩ := hr
              have hr := cometReturnBool value (by decide) rd7
              simpa only [hs'.accounts] using hr
        · simp only [CollateralCheckPublicResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 8 ≤ 1024; decide) hc rd4
      · simp only [CollateralCheckPublicResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_1422_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 32) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [CollateralCheckPublicResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_1422_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 32) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [CollateralCheckPublicResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_1415_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
