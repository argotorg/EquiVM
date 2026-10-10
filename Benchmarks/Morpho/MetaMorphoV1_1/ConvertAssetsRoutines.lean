import Benchmarks.Morpho.MetaMorphoV1_1.ConvertAssetsSource
import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_071

/-! Runtime execution of asset conversion with all checked arithmetic failures. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem convertAssetsNumeratorPrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares supply total ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (ht : total.toNat + 1 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨15343⟩
      ([shares, supply, total, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨15355⟩
      ([shares, supply, total + ⟨1⟩, ret] ++ R) mem aw' rdata σ k' C' := by
  exact metaMorphoV1_1_block_15343_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by
      change UInt256.gt total (total + ⟨1⟩) = ⟨0⟩
      rw [u256_add_comm total ⟨1⟩]
      exact checkedAddNoOverflowGt total ⟨1⟩ ht) rd

theorem convertAssetsScalePrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares supply numerator ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 12 ≤ 1024)
    (ho : v.DECIMALS_OFFSET.toNat ≤ 77)
    (rd : RD (deployedRuntime v) I g s0 ⟨15355⟩
      ([shares, supply, numerator, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12077⟩
      ([supply, decimalScale v.DECIMALS_OFFSET, ⟨15337⟩,
        numerator, shares, ⟨0⟩, ⟨11757⟩, ret] ++ R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15355_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_15355_stack, wordsOf_immStore_DECIMALS_OFFSET,
    wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := decimalScaleReturn v
    (by simp only [List.append, List.length_cons]; omega) ho
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  exact metaMorphoV1_1_block_12515_packed (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem convertAssetsReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares supply total ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hfit : convertAssetsFits v.DECIMALS_OFFSET shares supply total)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨15343⟩
      ([shares, supply, total, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (convertAssetsWord v.DECIMALS_OFFSET shares supply total :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := convertAssetsNumeratorPrefix v (by omega) hfit.2.2.1 rd
  obtain ⟨aw2, k2, C2, h2⟩ := convertAssetsScalePrefix v (by omega) hfit.1 h1
  obtain ⟨k3, C3, h3⟩ := checkedAddReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit.2.1
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
  obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_15337_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
  obtain ⟨aw5, k5, C5, h5⟩ := mathMulDivDownReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit.2.2.2
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h4
  exact metaMorphoV1_1_block_11757_packed (immWords := wordsOf (immStore v))
    (by omega) hret h5

theorem convertAssetsRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {shares supply total ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hbad : ¬ convertAssetsFits v.DECIMALS_OFFSET shares supply total)
    (rd : RD (deployedRuntime v) I g s0 ⟨15343⟩
      ([shares, supply, total, ret] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases ht : total.toNat + 1 < UInt256.size
  · obtain ⟨aw1, k1, C1, h1⟩ := convertAssetsNumeratorPrefix v (by omega) ht rd
    by_cases ho : v.DECIMALS_OFFSET.toNat ≤ 77
    · obtain ⟨aw2, k2, C2, h2⟩ := convertAssetsScalePrefix v (by omega) ho h1
      by_cases hs : supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size
      · obtain ⟨k3, C3, h3⟩ := checkedAddReturn v
          (by simp only [List.append, List.length_cons]; omega) hs
          (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
        obtain ⟨aw4, k4, C4, h4⟩ := metaMorphoV1_1_block_15337_packed
          (immWords := wordsOf (immStore v))
          (by simp only [List.append, List.length_cons]; omega)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h3
        exact mathMulDivDownRevert v (by simp only [List.append, List.length_cons]; omega)
          (fun hd ↦ hbad ⟨ho, hs, ht, hd⟩) h4
      · exact checkedAddRevert v (by simp only [List.append, List.length_cons]; omega)
          (Nat.le_of_not_gt hs) h2
    · obtain ⟨aw2, k2, C2, h2⟩ := metaMorphoV1_1_block_15355_packed
        (immWords := wordsOf (immStore v))
        (by simp only [List.append, List.length_cons]; omega)
        (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
      simp only [metaMorphoV1_1_block_15355_stack, wordsOf_immStore_DECIMALS_OFFSET,
        wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at h2
      exact decimalScaleRevert v (by simp only [List.append, List.length_cons]; omega)
        v.decimalsOffset_lt (by omega) h2
  · have hg : UInt256.gt total (total + ⟨1⟩) = ⟨1⟩ := by
      simpa only [u256_add_comm total ⟨1⟩] using
        checkedAddOverflowGt total ⟨1⟩ (Nat.le_of_not_gt ht)
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15343_taken_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by change UInt256.gt total (total + ⟨1⟩) ≠ ⟨0⟩; rw [hg]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact metaMorphoV1_1_block_9453 (immWords := wordsOf (immStore v))
      (by change R.length + 4 + 2 ≤ 1024; omega) h1

end Benchmarks.Morpho.MetaMorphoV1_1
