import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopState
import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsQueueRoutines
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_072
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_073

/-! Queue indexing, saturating subtraction, and withdrawal-loop exit paths. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false
set_option maxRecDepth 2000

theorem withdrawLoopQueueRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {morpho i original assets : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 14 ≤ 1024)
    (hbound : i.toNat < (codeOwnerStorageWord I σ ⟨21⟩).toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨15998⟩
      ([morpho, i, original, assets] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨16116⟩
      ([accruedAssetsIdWord I σ i, ⟨16034⟩, ⟨16043⟩, ⟨16063⟩,
        accruedAssetsIdWord I σ i, ⟨16069⟩, assets, morpho, original, i] ++ R)
      (wordAt0Mem ⟨21⟩ mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_15998_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨k2, C2, h2⟩ := withdrawQueueIndex v
    (by simp only [List.append, List.length_cons]; omega) hbound
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h1
  obtain ⟨aw3, k3, C3, h3⟩ := metaMorphoV1_1_block_16012_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.append, List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
  have hshift : UInt256.shiftRight
      (codeOwnerStorageWord I σ (accruedAssetsQueueSlot i))
        (UInt256.shiftLeft ⟨0⟩ (UInt256.ofNat 3)) = accruedAssetsIdWord I σ i :=
    wordShiftRight_zero _
  dsimp only [codeOwnerStorageWord, accruedAssetsQueueSlot] at hshift
  exact ⟨aw3, k3, C3, by simpa only [metaMorphoV1_1_block_16012_stack, hshift] using h3⟩

theorem withdrawLoopRemainingRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {liquid assets morpho original i : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨16069⟩
      ([liquid, assets, morpho, original, i] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0
      (if withdrawRemainingWord assets liquid = ⟨0⟩ then ⟨16091⟩ else ⟨16083⟩)
      ([i, morpho, original, withdrawRemainingWord assets liquid] ++ R)
      mem aw' rdata σ k' C' := by
  by_cases hz : withdrawRemainingWord assets liquid = ⟨0⟩
  · rw [if_pos hz]
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16069_taken_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
      (by rw [wordZeroFloorSub, show UInt256.ofNat (assets.toNat - liquid.toNat) =
            withdrawRemainingWord assets liquid from rfl, hz]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact ⟨aw1, k1, C1, by simpa only [metaMorphoV1_1_block_16069_taken_stack,
      wordZeroFloorSub] using h1⟩
  · rw [if_neg hz]
    obtain ⟨aw1, k1, C1, h1⟩ := metaMorphoV1_1_block_16069_fallthrough_packed
      (immWords := wordsOf (immStore v)) (by simp only [List.append]; omega)
      (by rw [wordZeroFloorSub]; exact isZero_eq_zero_of_ne hz) rd
    exact ⟨aw1, k1, C1, by simpa only [metaMorphoV1_1_block_16069_fallthrough_stack,
      wordZeroFloorSub] using h1⟩

theorem withdrawLoopExitRoutine {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b original assets total supply len : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 7 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨15984⟩
      ([a, b, original, assets, total, supply, len] ++ R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ⟨12234⟩
      ([original, assets, ⟨12410⟩, total, supply] ++ R) mem aw' rdata σ k' C' := by
  exact metaMorphoV1_1_block_15984_packed (immWords := wordsOf (immStore v))
    (by simp only [List.append]; exact hstack)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
