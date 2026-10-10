import Benchmarks.Morpho.MetaMorphoV1_1.Decode
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_055
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_056
import Benchmarks.EAS.Attester.ArrayBounds

/-! The shared runtime decoder returning a view of a calldata word array. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1

open Benchmarks.EAS.Attester (ArrayHeadChecks)

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option maxRecDepth 2000

theorem calldataArrayView {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem out : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat}
    {head ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨11227⟩
      (head :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw out σ k C) :
    (¬ ArrayHeadChecks I.calldata head ∧ RDrev (deployedRuntime v) g s0) ∨
    (ArrayHeadChecks I.calldata head ∧ ∃ k' C',
      RD (deployedRuntime v) I g s0 ret
        (calldataWord I.calldata head.toNat :: (head + ⟨32⟩) :: R)
        mem aw out σ k' C') := by
  by_cases hhead :
      UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat I.calldata.size) = ⟨0⟩
  case pos =>
    have h := metaMorphoV1_1_block_11227_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [hhead]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
    exact .inl ⟨fun hc ↦ hc.header hhead,
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_11227_taken_stack, List.length_cons]; omega) h⟩
  have r1 := metaMorphoV1_1_block_11227_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (isZero_eq_zero_of_ne hhead) rd
  by_cases hlen : UInt256.gt (calldataWord I.calldata head.toNat)
      (UInt256.ofNat 18446744073709551615) = ⟨0⟩
  case neg =>
    have h := metaMorphoV1_1_block_11240_taken (immWords := wordsOf (immStore v))
      (by omega) hlen
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r1
    exact .inl ⟨fun hc ↦ hlen (u256_isZero_ne_zero_to_eq_zero hc.length),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_11240_taken_stack, List.length_cons]; omega) h⟩
  have r2 := metaMorphoV1_1_block_11240_fallthrough (immWords := wordsOf (immStore v))
    (by omega) hlen r1
  by_cases hend : UInt256.gt
      ((head + UInt256.shiftLeft (calldataWord I.calldata head.toNat) (UInt256.ofNat 5)) +
        UInt256.ofNat 32)
      (UInt256.ofNat I.calldata.size) = ⟨0⟩
  case neg =>
    have h := metaMorphoV1_1_block_11257_taken (immWords := wordsOf (immStore v))
      (by omega) (by rw [u256_add_comm (UInt256.shiftLeft _ _) head]; exact hend)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) r2
    exact .inl ⟨fun hc ↦ hend (u256_isZero_ne_zero_to_eq_zero hc.payload),
      metaMorphoV1_1_block_917 (immWords := wordsOf (immStore v))
        (by simp only [metaMorphoV1_1_block_11257_taken_stack, List.length_cons]; omega) h⟩
  have r3 := metaMorphoV1_1_block_11257_fallthrough (immWords := wordsOf (immStore v))
    (by omega) (by rw [u256_add_comm (UInt256.shiftLeft _ _) head]; exact hend) r2
  have r4 := metaMorphoV1_1_block_11274 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hret r3
  exact .inr ⟨⟨hhead, by rw [hlen]; decide, by rw [hend]; decide⟩, _, _, r4⟩

end Benchmarks.Morpho.MetaMorphoV1_1
