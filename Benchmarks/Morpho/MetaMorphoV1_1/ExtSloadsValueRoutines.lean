import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsDecodedMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_045
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_057

/-! Read the first decoded slot, or revert on an empty array, at the supply-share continuation. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables metaMorphoV1_1Blocks

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem extSloadsValueReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {out : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hcheck : extSloadsReturnChecks out) (hfit : allocationFits ptr (extSloadsArraySize out))
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨14256⟩ (ptr :: ⟨14232⟩ :: ret :: R)
      (extSloadsDecodedMem mem ptr out) aw out σ k C) :
    (extSloadsReturnCount out = 0 ∧ RDrev (deployedRuntime v) g s0) ∨
      (0 < extSloadsReturnCount out ∧ ∃ aw' k' C',
        RD (deployedRuntime v) I g s0 ret
          (calldataWord out (extSloadsReturnOffset out + 32) :: R)
          (extSloadsDecodedMem mem ptr out) aw' out σ k' C') := by
  have h1 := metaMorphoV1_1_block_14256 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  have h2 := metaMorphoV1_1_block_9138 (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h1
  by_cases hzero : extSloadsReturnCount out = 0
  · have hpanic := metaMorphoV1_1_block_12044_taken
      (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
      (by rw [extSloadsDecodedMem_length, hzero]; decide)
      (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) h2
    exact .inl ⟨hzero, metaMorphoV1_1_block_11515 (immWords := wordsOf (immStore v))
      (by simp only [List.length_cons]; omega) hpanic⟩
  · have hn : 0 < extSloadsReturnCount out := by omega
    have hcount := hcheck.length
    have hcfit : extSloadsReturnCount out < UInt256.size := by
      change extSloadsReturnCount out ≤ 18446744073709551615 at hcount
      change _ < 2 ^ 256
      omega
    have hlen : memLoad ptr (extSloadsDecodedMem mem ptr out) ≠ ⟨0⟩ := by
      rw [extSloadsDecodedMem_length]
      intro hz
      have he := congrArg UInt256.toNat hz
      rw [UInt256.toNat_ofNat_of_lt hcfit] at he
      exact hzero he
    obtain ⟨aw1, k1, C1, h3⟩ := firstArrayElementReturn v
      (by simp only [List.length_cons]; omega) hlen
      (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) h2
    obtain ⟨aw2, k2, C2, h4⟩ := metaMorphoV1_1_block_14232_packed
      (immWords := wordsOf (immStore v)) (by omega) hret h3
    have hb := extSloadsArrayBound hcheck.length hfit
    have hp : ptr.toNat + 32 < UInt256.size := by change _ < 2 ^ 256; omega
    exact .inr ⟨hn, aw2, k2, C2, by
      simpa only [metaMorphoV1_1_block_14232_stack, extSloadsDecodedMem_first mem ptr out hn hp]
        using h4⟩

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
