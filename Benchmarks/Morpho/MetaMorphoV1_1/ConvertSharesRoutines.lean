import Benchmarks.Morpho.MetaMorphoV1_1.ConvertSharesSource
import Benchmarks.Morpho.MetaMorphoV1_1.DecimalScaleRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.MathMulDivDownRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_062

/-! Runtime execution of share conversion, including every checked arithmetic failure. -/

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem convertSharesScalePrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets supply total ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (ho : v.DECIMALS_OFFSET.toNat ≤ 77)
    (rd : RD (deployedRuntime v) I g s0 ⟨14489⟩
      ([assets, supply, total, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12077⟩
      ([supply, decimalScale v.DECIMALS_OFFSET, ⟨14535⟩, assets, total, ret] ++ R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14489_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [metaMorphoV1_1_block_14489_stack, wordsOf_immStore_DECIMALS_OFFSET,
    wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at h1
  obtain ⟨aw2, k2, C2, h2⟩ := decimalScaleReturn v
    (by simp only [List.append, List.length_cons]; omega) ho
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  exact metaMorphoV1_1_block_12515_packed (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2

theorem convertSharesDenominatorPrefix {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets numerator total ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (ht : total.toNat + 1 < UInt256.size)
    (rd : RD (deployedRuntime v) I g s0 ⟨14535⟩
      ([numerator, assets, total, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨17811⟩
      ([assets, numerator, total + ⟨1⟩, ⟨0⟩, ⟨11757⟩, ret] ++ R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14535_fallthrough_packed
    (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by
      change UInt256.gt total (total + ⟨1⟩) = ⟨0⟩
      rw [u256_add_comm total ⟨1⟩]
      exact checkedAddNoOverflowGt total ⟨1⟩ ht) rd
  exact metaMorphoV1_1_block_14548_packed (immWords := wordsOf (immStore v))
    (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1

theorem convertSharesReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets supply total ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hfit : convertSharesFits v.DECIMALS_OFFSET assets supply total)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14489⟩
      ([assets, supply, total, ret] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret
      (convertSharesWord v.DECIMALS_OFFSET assets supply total :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := convertSharesScalePrefix v (by omega) hfit.1 rd
  obtain ⟨k2, C2, h2⟩ := checkedAddReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit.2.1
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := convertSharesDenominatorPrefix v (by omega) hfit.2.2.1 h2
  obtain ⟨aw4, k4, C4, h4⟩ := mathMulDivDownReturn v
    (by simp only [List.append, List.length_cons]; omega) hfit.2.2.2
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h3
  exact metaMorphoV1_1_block_11757_packed (immWords := wordsOf (immStore v))
    (by omega) hret h4

theorem convertSharesRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {assets supply total ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 18 ≤ 1024)
    (hbad : ¬ convertSharesFits v.DECIMALS_OFFSET assets supply total)
    (rd : RD (deployedRuntime v) I g s0 ⟨14489⟩
      ([assets, supply, total, ret] ++ R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  by_cases ho : v.DECIMALS_OFFSET.toNat ≤ 77
  · obtain ⟨aw1, k1, C1, h1⟩ := convertSharesScalePrefix v (by omega) ho rd
    by_cases hs : supply.toNat + (decimalScale v.DECIMALS_OFFSET).toNat < UInt256.size
    · obtain ⟨k2, C2, h2⟩ := checkedAddReturn v
        (by simp only [List.append, List.length_cons]; omega) hs
        (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
      by_cases ht : total.toNat + 1 < UInt256.size
      · obtain ⟨aw3, k3, C3, h3⟩ := convertSharesDenominatorPrefix v (by omega) ht h2
        exact mathMulDivDownRevert v (by simp only [List.append, List.length_cons]; omega)
          (fun hd ↦ hbad ⟨ho, hs, ht, hd⟩) h3
      · have hg : UInt256.gt total (total + ⟨1⟩) = ⟨1⟩ := by
          simpa only [u256_add_comm total ⟨1⟩] using
            checkedAddOverflowGt total ⟨1⟩ (Nat.le_of_not_gt ht)
        obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_14535_taken_packed
          (immWords := wordsOf (immStore v))
          (by simp only [List.append, List.length_cons]; omega)
          (by change UInt256.gt total (total + ⟨1⟩) ≠ ⟨0⟩; rw [hg]; decide)
          (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
        exact metaMorphoV1_1_block_9453 (immWords := wordsOf (immStore v))
          (by change R.length + 4 + 2 ≤ 1024; omega) h3
    · exact checkedAddRevert v (by simp only [List.append, List.length_cons]; omega)
        (Nat.le_of_not_gt hs) h1
  · obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_14489_packed
      (immWords := wordsOf (immStore v))
      (by simp only [List.append, List.length_cons]; omega)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    simp only [metaMorphoV1_1_block_14489_stack, wordsOf_immStore_DECIMALS_OFFSET,
      wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat] at h1
    exact decimalScaleRevert v (by simp only [List.append, List.length_cons]; omega)
      v.decimalsOffset_lt (by omega) h1

end Benchmarks.Morpho.MetaMorphoV1_1
