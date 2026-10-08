import Benchmarks.CompoundIII.Comet.Dispatch
import Benchmarks.CompoundIII.Comet.AccrualTimeEvm
import Benchmarks.CompoundIII.Comet.InitializeState
import Benchmarks.CompoundIII.Comet.InitializeStatic
import Benchmarks.CompoundIII.Comet.RuntimeBlocks_013

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.CompoundIII.Comet.Immutables
open cometWithExtendedAssetListBlocks

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def InitializeResult (code : ByteArray) (I : ExecutionEnv) (g : Sat256)
    (s0 : State) (σ : AccountMap) : Prop :=
  if I.weiValue = ⟨0⟩ ∧ I.calldata.size < 2^255 + 4 ∧
      lastAccrualWord (solcSlotWordAt ⟨1⟩ σ I) = ⟨0⟩ ∧ (timestampWord I).toNat < 2^40 then
    if I.perm = true then RDret code g s0 (initializeAccounts σ I) ByteArray.empty
    else RDstatic code g s0
  else RDrev code g s0

theorem initializeX {σ σ₀ A I} {g : Sat256} (v : CometWithExtendedAssetListImmutables)
    (hcode : I.code = deployedRuntime v) (hsz : 4 ≤ I.calldata.size)
    (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (cometWithExtendedAssetListSelBytes 6)) :
    InitializeResult (deployedRuntime v) I g (initState σ σ₀ g A I) σ := by
  obtain ⟨k, C, rd⟩ := cometWithExtendedAssetListReachInitializeStorageBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := g) v hcode hsz hsize hsel
  have rd1 := cometWithExtendedAssetList_block_1330 (immWords := wordsOf (immStore v))
    (by decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd
  by_cases hv : I.weiValue = ⟨0⟩
  · have rd2 := cometWithExtendedAssetList_block_1807_fallthrough
      (immWords := wordsOf (immStore v)) (by decide) hv rd1
    by_cases hhi : I.calldata.size < 2^255 + 4
    · have rd3 := cometWithExtendedAssetList_block_1814_fallthrough
        (immWords := wordsOf (immStore v)) (by decide)
        (by rw [u256_add_comm]; exact getterLength_ok hsz hhi hsize) rd2
      by_cases hz : lastAccrualWord (solcSlotWordAt ⟨1⟩ σ I) = ⟨0⟩
      · obtain ⟨k4, C4, rd4⟩ := cometWithExtendedAssetList_block_1827_fallthrough
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [lastAccrualWord_eq] at hz; exact hz) rd3
        have rd5 := cometWithExtendedAssetList_block_1845 (immWords := wordsOf (immStore v))
          (by change 5 ≤ 1024; decide) (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd4
        by_cases ht : (timestampWord I).toNat < 2^40
        · obtain ⟨k6, C6, rd6⟩ := cometNow (v := v) (by change 6 ≤ 1024; decide) ht
            (by rw [cometWithExtendedAssetListPatchedValidJumps v]; jump_dest) rd5
          unfold InitializeResult
          rw [if_pos ⟨hv, hhi, hz, ht⟩]
          by_cases hperm : I.perm = true
          · rw [if_pos hperm]
            have rd7 := cometWithExtendedAssetList_block_1861
              (immWords := wordsOf (immStore v)) (by decide) hperm rd6
            change RDret _ _ _ (initializeAccounts σ I)
              (solcFreePtrMem.readWithPadding (memLoad ⟨64⟩ solcFreePtrMem).toNat 0) at rd7
            rw [byteArray_readWithPadding_zero] at rd7
            exact rd7
          · rw [if_neg hperm]
            exact cometInitializeStatic (v := v) (by decide) (Bool.eq_false_iff.mpr hperm) rd6
        · simp only [InitializeResult, ht, and_false, if_false]
          exact cometNow_revert (v := v) (by change 7 ≤ 1024; decide) ht rd5
      · simp only [InitializeResult, hz, false_and, and_false, if_false]
        obtain ⟨k4, C4, rd4⟩ := cometWithExtendedAssetList_block_1827_taken
          (immWords := wordsOf (immStore v)) (by decide)
          (by rw [lastAccrualWord_eq] at hz; exact hz)
          (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd3
        exact cometWithExtendedAssetList_block_1921
          (immWords := wordsOf (immStore v)) (by change 5 ≤ 1024; decide) rd4
    · simp only [InitializeResult, hhi, false_and, and_false, if_false]
      have rd3 := cometWithExtendedAssetList_block_1814_taken
        (immWords := wordsOf (immStore v)) (by decide)
        (by rw [u256_add_comm]; exact getterLength_huge (by omega) hsize)
        (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd2
      exact cometWithExtendedAssetList_block_1938
        (immWords := wordsOf (immStore v)) (by decide) rd3
  · simp only [InitializeResult, hv, false_and, if_false]
    have rd2 := cometWithExtendedAssetList_block_1807_taken
      (immWords := wordsOf (immStore v)) (by decide) hv
      (by rw [cometWithExtendedAssetListPatchedValidJumpsRuntime v]; jump_dest) rd1
    exact cometRevert1410 (by decide) rd2

end Benchmarks.CompoundIII.Comet
