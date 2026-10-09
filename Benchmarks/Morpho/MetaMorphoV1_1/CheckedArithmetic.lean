import Benchmarks.Morpho.MetaMorphoV1_1.Arithmetic
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_060
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_046
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_074

/-! Shared checked arithmetic routines emitted by the pinned compiler. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode

set_option maxRecDepth 2000 in
theorem checkedMulReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hfit : a.toNat * b.toNat < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12002⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (UInt256.mul a b :: R)
      mem aw rdata σ k' C' := by
  have rd12020 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12002_fallthrough
    (immWords := wordsOf (immStore v)) hstack (checkedMulGuardOk a b hfit) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12020
    (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hvalid rd12020
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem checkedMulRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 6 ≤ 1024)
    (hover : UInt256.size ≤ a.toNat * b.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12002⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd9453 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12002_taken
    (immWords := wordsOf (immStore v)) hstack (checkedMulGuardOverflow a b hover)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_9453
    (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_12002_taken_stack,
        List.length_cons]; omega) rd9453

set_option maxRecDepth 2000 in
theorem checkedAddReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hfit : a.toNat + b.toNat < UInt256.size)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨12077⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have rd12089 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12077_fallthrough
    (immWords := wordsOf (immStore v)) hstack (by
      simpa only [u256_add_comm b a] using checkedAddNoOverflowGt a b hfit) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12089
    (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) hvalid rd12089
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem checkedAddRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (hover : UInt256.size ≤ a.toNat + b.toNat)
    (rd : RD (deployedRuntime v) I g s0 ⟨12077⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd9453 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_12077_taken
    (immWords := wordsOf (immStore v)) hstack (by
      change UInt256.gt a (a + b) ≠ ⟨0⟩
      rw [u256_add_comm a b, checkedAddOverflowGt a b hover]
      decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_9453
    (immWords := wordsOf (immStore v))
    (by simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_12077_taken_stack,
        List.length_cons]; omega) rd9453

set_option maxRecDepth 2000 in
theorem checkedDivReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a b ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 5 ≤ 1024) (hden : b ≠ ⟨0⟩)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16368⟩ (a :: b :: ret :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ret (UInt256.div a b :: R)
      mem aw rdata σ k' C' := by
  have rd16375 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_16368_fallthrough
    (immWords := wordsOf (immStore v)) (by simpa using hstack)
    (isZero_eq_zero_of_ne hden) rd
  have hret := metaMorphoV1_1Blocks.metaMorphoV1_1_block_16375
    (immWords := wordsOf (immStore v)) (by omega) hvalid rd16375
  exact ⟨_, _, hret⟩

set_option maxRecDepth 2000 in
theorem checkedDivRevert {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {a : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 4 ≤ 1024)
    (rd : RD (deployedRuntime v) I g s0 ⟨16368⟩ (a :: ⟨0⟩ :: R) mem aw rdata σ k C) :
    RDrev (deployedRuntime v) g s0 := by
  have rd16378 := metaMorphoV1_1Blocks.metaMorphoV1_1_block_16368_taken
    (immWords := wordsOf (immStore v)) hstack (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  exact metaMorphoV1_1Blocks.metaMorphoV1_1_block_16378
    (immWords := wordsOf (immStore v)) (by simpa using hstack) rd16378

end Benchmarks.Morpho.MetaMorphoV1_1
