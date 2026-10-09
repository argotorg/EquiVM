import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.WithdrawReservesInternal
import Benchmarks.CompoundIII.Comet.AbiRoutines
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_008
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_032
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_021

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def WithdrawReservesResult (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv)
    (g : Sat256) (s0 : EVM.State) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ 68 ≤ I.calldata.size ∧ I.calldata.size < 2^255 + 4 ∧
      (calldataWord I.calldata 4).toNat < EVM.addressModulus then
    ∃ result, WithdrawReservesTrace v (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (calldataWord I.calldata 36) s0 result ∧ WithdrawReservesRun v g s0 result
  else RDrev (deployedRuntime v) g s0

theorem withdrawReservesX {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 63)) :
    WithdrawReservesResult v I g (initState σ σ₀ g A I) := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachWithdrawReservesBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_817 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_6117_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hlo : 68 ≤ I.calldata.size
    · by_cases hhi : I.calldata.size < 2^255 + 4
      · have rd3 := cometWithExtendedAssetList_block_6124_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_ok (need := 64) (by decide) hlo hhi hsize) rd2
        have rd4 := cometWithExtendedAssetList_block_6136
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        by_cases hc : (calldataWord I.calldata 4).toNat < EVM.addressModulus
        · obtain ⟨k5, C5, rd5⟩ := cometValidateAddress_ok (v := v)
            (ret := UInt256.ofNat 6147) (by change 6 ≤ 1024; decide) hc
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd4
          have hgov : UInt256.land
              (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
                (UInt256.ofNat 1)) (wordsOf (immStore v) "governor") = EVM.word v.governor.val := by
            rw [wordsOf_immStore_governor]
            exact solcAddrMask_clean_left (addressWord_val_canonical v.governor)
          unfold WithdrawReservesResult
          rw [if_pos ⟨hv, hlo, hhi, hc⟩]
          by_cases ha : I.source = v.governor
          · have rd6 := cometWithExtendedAssetList_block_6147_fallthrough
              (immWords := wordsOf (immStore v)) (by decide)
              (by rw [hgov, ha]; exact u256_sub_self _) rd5
            change RD _ _ _ _ _ [solcAddrMask, calldataWord I.calldata 4,
              calldataWord I.calldata 36] _ _ _ _ _ _ at rd6
            rw [← addressWord_eq_ofNat_address hc] at rd6
            exact cometWithdrawReservesQuery (v := v) (by change 38 ≤ 1024; decide)
              solcFreePtrMem_mload64 (by decide) (by decide) ha SourceState.init rd6
          · have hn : UInt256.sub (UInt256.ofNat I.source.val) (EVM.word v.governor.val) ≠ ⟨0⟩ := by
              intro he
              have heq := u256_sub_eq_zero_iff_eq.mp he
              change UInt256.ofNat I.source.val = UInt256.ofNat v.governor.val at heq
              have ht := congrArg AccountAddress.ofUInt256 heq
              exact ha (by simpa only [accountAddress_roundtrip] using ht)
            have rd6 := cometWithExtendedAssetList_block_6147_taken
              (immWords := wordsOf (immStore v)) (by decide) (by rw [hgov]; exact hn)
              (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd5
            exact ⟨none, .unauthorized ha,
              cometWithExtendedAssetList_block_3682 (immWords := wordsOf (immStore v))
                (by change 6 ≤ 1024; decide) rd6⟩
        · simp only [WithdrawReservesResult, hc, and_false, if_false]
          exact cometValidateAddress_bad (v := v) (by change 6 ≤ 1024; decide) hc rd4
      · simp only [WithdrawReservesResult, hhi, false_and, and_false, if_false]
        have rd3 := cometWithExtendedAssetList_block_6124_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (calldataLength_huge (need := 64) (by decide) (by omega) hsize)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
        exact cometRevert1410 (by decide) rd3
    · simp only [WithdrawReservesResult, hlo, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_6124_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (calldataLength_short (need := 64) (by decide) hsz (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometRevert1410 (by decide) rd3
  · simp only [WithdrawReservesResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_6117_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
