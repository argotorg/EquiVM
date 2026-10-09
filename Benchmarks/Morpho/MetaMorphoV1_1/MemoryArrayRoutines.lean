import Benchmarks.Morpho.MetaMorphoV1_1.MemoryArrayData
import Benchmarks.Morpho.MetaMorphoV1_1.MemoryRoutines

/-! The EVM routine constructing a singleton array, with its final memory contents. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

set_option maxRecDepth 2000 in
theorem morphoArrayReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {ptr value ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 9 ≤ 1024)
    (hcalldata : I.calldata.size < UInt256.size)
    (hfree : memLoad ⟨64⟩ mem = ptr) (hfit : ptr.toNat + 64 < 2 ^ 64)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨16791⟩ (value :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret (ptr :: R)
      (morphoArrayMem mem I.calldata ptr value) aw' rdata σ k' C' := by
  have halloc := metaMorphoV1_1Blocks.metaMorphoV1_1_block_16791
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) rd
  change RD _ _ _ _ _
    (memLoad ⟨64⟩ mem :: ⟨64⟩ :: ⟨16806⟩ :: value :: memLoad ⟨64⟩ mem :: ret :: R)
    _ _ _ _ _ _ at halloc
  rw [hfree] at halloc
  obtain ⟨_, _, _, hinit⟩ := allocateReturn v (by simp only [List.length_cons]; omega)
    (by decide) hfit (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) halloc
  obtain ⟨aw1, k1, C1, hindex⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_16806_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hinit
  have hm : metaMorphoV1_1Blocks.metaMorphoV1_1_block_16806_memory (ee := I)
      (mem := writeWord mem 64 (ptr + ⟨64⟩)) (x1 := ptr) =
      morphoArrayInitMem mem I.calldata ptr := by
    unfold metaMorphoV1_1Blocks.metaMorphoV1_1_block_16806_memory
    rw [UInt256.toNat_ofNat_of_lt hcalldata]
    rfl
  simp only [metaMorphoV1_1Blocks.metaMorphoV1_1_block_16806_stack, hm] at hindex
  have h32 : ptr.toNat + 32 < UInt256.size :=
    lt_trans (by omega : ptr.toNat + 32 < 2 ^ 64) (by decide)
  obtain ⟨_, _, _, hstore⟩ := firstArrayElementReturn v
    (by simp only [List.length_cons]; omega)
    (by rw [morphoArrayInitMem_length mem I.calldata ptr h32]; decide)
    (by rw [metaMorphoV1_1PatchedValidJumps v]; jump_dest) hindex
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_16826_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hstore
  exact ⟨aw', k', C', hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1
