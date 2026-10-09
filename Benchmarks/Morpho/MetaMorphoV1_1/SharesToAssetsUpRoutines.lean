import Benchmarks.Morpho.MetaMorphoV1_1.SharesToAssetsUp
import Benchmarks.Morpho.MetaMorphoV1_1.CheckedArithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_078
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_079
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_077
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_058

/-! Bytecode proof of Morpho's rounded-up share-to-asset conversion. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000

theorem assetsUpDenominatorFacts (totalShares : UInt256)
    (hfit : totalShares.toNat + 1000000 < UInt256.size) :
    totalShares + UInt256.ofNat 1000000 ≠ ⟨0⟩ ∧
      UInt256.sub (totalShares + UInt256.ofNat 1000000) ⟨1⟩ =
        totalShares + UInt256.ofNat 999999 ∧
      (totalShares + UInt256.ofNat 999999).toNat ≤
        (totalShares + UInt256.ofNat 1000000).toNat := by
  have hden : (totalShares + UInt256.ofNat 1000000).toNat = totalShares.toNat + 1000000 :=
    addWord_toNat _ _ hfit
  have hpred : (totalShares + UInt256.ofNat 999999).toNat = totalShares.toNat + 999999 :=
    addWord_toNat _ _ (by change totalShares.toNat + 999999 < UInt256.size; omega)
  refine ⟨?_, ?_, ?_⟩
  · intro hz
    have hh := congrArg UInt256.toNat hz
    rw [hden] at hh
    change totalShares.toNat + 1000000 = 0 at hh
    omega
  · rw [subOne_eq_addNotZero, u256_add_assoc]
    rfl
  · rw [hden, hpred]
    omega

theorem assetsUpReachShares {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (ha : assets.toNat + 1 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨17655⟩ (shares :: assets :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨17668⟩ ((assets + ⟨1⟩) :: shares :: R)
      mem aw rdata σ k' C' := by
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17655_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      simpa only [u256_add_comm (⟨1⟩ : UInt256) assets] using
        checkedAddNoOverflowGt assets ⟨1⟩ ha) rd
  exact ⟨_, _, hret⟩

theorem assetsUpReachMultiply {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets totalShares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (ha : assets.toNat + 1 < UInt256.size)
    (hs : totalShares.toNat + 1000000 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨17655⟩
      (shares :: assets :: totalShares :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12002⟩
      (shares :: (assets + ⟨1⟩) :: ⟨17695⟩ :: UInt256.ofNat 999999 ::
        (totalShares + UInt256.ofNat 1000000) :: totalShares :: ret :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, rd17668⟩ := assetsUpReachShares v (by simp only [List.length_cons]; omega) ha rd
  have rd17682 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17668_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by
      simpa only [u256_add_comm (UInt256.ofNat 1000000) totalShares] using
        checkedAddNoOverflowGt totalShares (UInt256.ofNat 1000000) hs) rd17668
  have rd12002 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17682
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd17682
  exact ⟨_, _, rd12002⟩

theorem assetsUpReachAdd {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {prod totalShares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (hs : totalShares.toNat + 1000000 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨17695⟩
      (prod :: UInt256.ofNat 999999 :: (totalShares + UInt256.ofNat 1000000) ::
        totalShares :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨12077⟩
      (prod :: UInt256.sub (totalShares + UInt256.ofNat 1000000) ⟨1⟩ :: ⟨17503⟩ ::
        (totalShares + UInt256.ofNat 1000000) :: ⟨11757⟩ :: ret :: R)
      mem aw rdata σ k' C' := by
  have hfacts := assetsUpDenominatorFacts totalShares hs
  have rd17706 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17695_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (ugt_zero hfacts.2.2) rd
  have rd12077 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17706
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd17706
  change RD _ _ _ _ _
    (prod :: (totalShares + UInt256.ofNat 999999) :: ⟨17503⟩ ::
      (totalShares + UInt256.ofNat 1000000) :: ⟨11757⟩ :: ret :: R) _ _ _ _ _ _ at rd12077
  rw [← hfacts.2.1] at rd12077
  exact ⟨_, _, rd12077⟩

theorem assetsUpReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets totalShares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hfit : assetsUpFits shares assets totalShares)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨17655⟩
      (shares :: assets :: totalShares :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (assetsUpWord shares assets totalShares :: R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, rd12002⟩ := assetsUpReachMultiply v hstack hfit.1 hfit.2.1 rd
  obtain ⟨_, _, rd17695⟩ := checkedMulReturn v
    (by simp only [List.length_cons]; omega) hfit.2.2.1
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12002
  obtain ⟨_, _, rd12077⟩ := assetsUpReachAdd v (by omega) hfit.2.1 rd17695
  obtain ⟨_, _, rd17503⟩ := checkedAddReturn v
    (by simp only [List.length_cons]; omega) hfit.2.2.2.2
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12077
  have rd16368 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17503
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd17503
  obtain ⟨_, _, rd11757⟩ := checkedDivReturn v
    (by simp only [List.length_cons]; omega) hfit.2.2.2.1
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd16368
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_11757
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd11757
  exact ⟨_, _, hret⟩

theorem assetsUpRevertAssets {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (ha : UInt256.size ≤ assets.toNat + 1)
    (rd : RD (deployedRuntime v) I g s0 ⟨17655⟩ (shares :: assets :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd9453 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17655_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.gt assets (assets + ⟨1⟩) ≠ ⟨0⟩
      rw [u256_add_comm assets ⟨1⟩, checkedAddOverflowGt assets ⟨1⟩ ha]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_9453
    (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_17655_taken_stack,
        List.length_cons]; omega) rd9453

theorem assetsUpRevertShares {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets totalShares : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hs : UInt256.size ≤ totalShares.toNat + 1000000)
    (rd : RD (deployedRuntime v) I g s0 ⟨17668⟩
      (assets :: shares :: totalShares :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd9453 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_17668_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.gt totalShares (totalShares + UInt256.ofNat 1000000) ≠ ⟨0⟩
      rw [u256_add_comm totalShares (UInt256.ofNat 1000000),
        checkedAddOverflowGt totalShares (UInt256.ofNat 1000000) hs]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_9453
    (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_17668_taken_stack,
        List.length_cons]; omega) rd9453

theorem assetsUpRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares assets totalShares ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 10 ≤ 1024)
    (hfail : ¬ assetsUpFits shares assets totalShares)
    (rd : RD (deployedRuntime v) I g s0 ⟨17655⟩
      (shares :: assets :: totalShares :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases ha : assets.toNat + 1 < UInt256.size
  · by_cases hs : totalShares.toNat + 1000000 < UInt256.size
    · obtain ⟨_, _, rd12002⟩ := assetsUpReachMultiply v hstack ha hs rd
      by_cases hprod : shares.toNat * (assets + ⟨1⟩).toNat < UInt256.size
      · obtain ⟨_, _, rd17695⟩ := checkedMulReturn v
          (by simp only [List.length_cons]; omega) hprod
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) rd12002
        obtain ⟨_, _, rd12077⟩ := assetsUpReachAdd v (by omega) hs rd17695
        have hden := (assetsUpDenominatorFacts totalShares hs).1
        have hover : UInt256.size ≤ (UInt256.mul shares (assets + ⟨1⟩)).toNat +
            (UInt256.sub (totalShares + UInt256.ofNat 1000000) ⟨1⟩).toNat := by
          exact Nat.le_of_not_gt (fun hsum ↦ hfail ⟨ha, hs, hprod, hden, hsum⟩)
        exact checkedAddRevert v (by simp only [List.length_cons]; omega) hover rd12077
      · exact checkedMulRevert v (by simp only [List.length_cons]; omega)
          (Nat.le_of_not_gt hprod) rd12002
    · obtain ⟨_, _, rd17668⟩ := assetsUpReachShares v
        (by simp only [List.length_cons]; omega) ha rd
      exact assetsUpRevertShares v (by simp only [List.length_cons]; omega)
        (Nat.le_of_not_gt hs) rd17668
  · exact assetsUpRevertAssets v (by simp only [List.length_cons]; omega)
      (Nat.le_of_not_gt ha) rd

end Benchmarks.Morpho.MetaMorphoV1_1
