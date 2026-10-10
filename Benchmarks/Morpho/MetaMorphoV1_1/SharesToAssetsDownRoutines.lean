import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsDown
import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsUpRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_082

/-! Morpho's rounded-down share-to-asset conversion, including each checked operation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem assetsDownReachShares {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets totalShares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024)
    (ha : assets.toNat + 1 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨18378⟩
      (shares :: assets :: totalShares :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18391⟩
      (shares :: totalShares :: (assets + ⟨1⟩) :: R) mem aw rdata σ k' C' := by
  have h := metaMorphoV1_1_block_18378_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      apply ult_zero
      have hn : (assets + UInt256.ofNat 1).toNat = assets.toNat + 1 :=
        addWord_toNat assets ⟨1⟩ ha
      rw [hn]
      omega) rd
  exact ⟨_, _, h⟩

theorem assetsDownReachMultiply {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets totalShares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (ha : assets.toNat + 1 < UInt256.size)
    (hs : totalShares.toNat + 1000000 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨18378⟩
      (shares :: assets :: totalShares :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12002⟩
      (shares :: (assets + ⟨1⟩) :: ⟨17503⟩ ::
        (totalShares + UInt256.ofNat 1000000) :: ⟨11757⟩ :: ret :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, h1⟩ := assetsDownReachShares v (by simp only [List.length_cons]; omega) ha rd
  have h2 := metaMorphoV1_1_block_18391_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by
      simpa only [u256_add_comm (UInt256.ofNat 1000000) totalShares] using
        checkedAddNoOverflowGt totalShares (UInt256.ofNat 1000000) hs) h1
  have h3 := metaMorphoV1_1_block_18404
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  exact ⟨_, _, h3⟩

theorem assetsDownReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets totalShares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hfit : assetsDownFits shares assets totalShares)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨18378⟩
      (shares :: assets :: totalShares :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (assetsDownWord shares assets totalShares :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, h1⟩ := assetsDownReachMultiply v (by omega) hfit.1 hfit.2.1 rd
  obtain ⟨_, _, h2⟩ := checkedMulReturn v (by simp only [List.length_cons]; omega) hfit.2.2.1
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  have h3 := metaMorphoV1_1_block_17503
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  obtain ⟨_, _, h4⟩ := checkedDivReturn v (by simp only [List.length_cons]; omega) hfit.2.2.2
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
  exact ⟨_, _, metaMorphoV1_1_block_11757
    (immWords := wordsOf (immStore v)) (by omega) hret h4⟩

theorem assetsDownRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets totalShares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hfail : ¬ assetsDownFits shares assets totalShares)
    (rd : RD (deployedRuntime v) I g s0 ⟨18378⟩
      (shares :: assets :: totalShares :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases ha : assets.toNat + 1 < UInt256.size
  · by_cases hs : totalShares.toNat + 1000000 < UInt256.size
    · obtain ⟨_, _, h1⟩ := assetsDownReachMultiply v (by omega) ha hs rd
      have hprod : UInt256.size ≤ shares.toNat * (assets + ⟨1⟩).toNat :=
        Nat.le_of_not_gt (fun hp ↦ hfail ⟨ha, hs, hp, (assetsUpDenominatorFacts _ hs).1⟩)
      exact checkedMulRevert v (by simp only [List.length_cons]; omega) hprod h1
    · obtain ⟨_, _, h1⟩ := assetsDownReachShares v
        (by simp only [List.length_cons]; omega) ha rd
      have h2 := metaMorphoV1_1_block_18391_taken
        (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by
          change UInt256.gt totalShares (totalShares + UInt256.ofNat 1000000) ≠ ⟨0⟩
          rw [u256_add_comm totalShares (UInt256.ofNat 1000000),
            checkedAddOverflowGt totalShares (UInt256.ofNat 1000000) (Nat.le_of_not_gt hs)]
          decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      exact metaMorphoV1_1_block_9453 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_18391_taken_stack, List.length_cons]; omega) h2
  · have h1 := metaMorphoV1_1_block_18378_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by
        change UInt256.gt assets (assets + ⟨1⟩) ≠ ⟨0⟩
        rw [u256_add_comm assets ⟨1⟩, checkedAddOverflowGt assets ⟨1⟩ (Nat.le_of_not_gt ha)]
        decide) (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_9453 (immWords := wordsOf (immStore v))
      (by simp only [metaMorphoV1_1_block_18378_taken_stack, List.length_cons]; omega) h1

end Benchmarks.Morpho.MetaMorphoV1_1
