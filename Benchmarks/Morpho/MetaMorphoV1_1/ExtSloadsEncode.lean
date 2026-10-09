import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsMemory
import Benchmarks.Morpho.MetaMorphoV1_1.RuntimeBlocks_065

/-! The shared dynamic-array argument encoder, specialized to a singleton word array. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1

attribute [local irreducible] metaMorphoV1_1Bytecode
set_option autoImplicit false

def singletonEncodeMem (mem : ByteArray) (pos slot : UInt256) : ByteArray :=
  writeWord (writeWord (writeWord mem pos.toNat ⟨32⟩) (pos + ⟨32⟩).toNat ⟨1⟩)
    (pos + ⟨64⟩).toNat slot

set_option maxRecDepth 2000 in
theorem singletonArrayEncodeReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {pos array slot ret : UInt256} {R : List UInt256}
    (v : MetaMorphoV1_1Immutables) (hstack : R.length + 8 ≤ 1024)
    (hin : array.toNat + 64 ≤ mem.size) (hbelow : array.toNat + 64 ≤ pos.toNat)
    (hfit : pos.toNat + 96 < UInt256.size)
    (hlen : memLoad array mem = ⟨1⟩) (hslot : memLoad (array + ⟨32⟩) mem = slot)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD (deployedRuntime v) I g s0 ⟨13342⟩ (pos :: array :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD (deployedRuntime v) I g s0 ret ((pos + ⟨96⟩) :: R)
      (singletonEncodeMem mem pos slot) aw' rdata σ k' C' := by
  have harray32 : (array + ⟨32⟩).toNat = array.toNat + 32 :=
    uadd_word_ofNat_toNat array 32 (by omega)
  have hpos32 : (pos + ⟨32⟩).toNat = pos.toNat + 32 :=
    uadd_word_ofNat_toNat pos 32 (by omega)
  have hlen' : memLoad array (writeWord mem pos.toNat ⟨32⟩) = ⟨1⟩ := by
    rw [memLoad_write_above _ _ _ _ (by omega) (by omega), hlen]
  have hslot' : memLoad (array + ⟨32⟩)
      (writeWord (writeWord mem pos.toNat ⟨32⟩) (pos + ⟨32⟩).toNat ⟨1⟩) = slot := by
    rw [memLoad_write_above _ _ _ _
      (by rw [harray32, writeWord_sparse_size]; omega) (by rw [harray32, hpos32]; omega)]
    rw [memLoad_write_above _ _ _ _ (by rw [harray32]; omega) (by rw [harray32]; omega), hslot]
  have hm : metaMorphoV1_1Blocks.metaMorphoV1_1_block_13342_memory
      (mem := mem) (x0 := pos) (x1 := array) =
      writeWord (writeWord mem pos.toNat ⟨32⟩) (pos + ⟨32⟩).toNat ⟨1⟩ := by
    change writeWord (writeWord mem pos.toNat ⟨32⟩) (pos + ⟨32⟩).toNat
      (memLoad array (writeWord mem pos.toNat ⟨32⟩)) = _
    rw [hlen']
  obtain ⟨_, _, _, hloop⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_13342_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) rd
  have hs : metaMorphoV1_1Blocks.metaMorphoV1_1_block_13342_stack
      (mem := mem) (x0 := pos) (x1 := array) (R := ret :: R) =
      (⟨0⟩ :: ⟨1⟩ :: (array + ⟨32⟩) :: (pos + ⟨64⟩) :: ret :: R) := by
    change (⟨0⟩ :: memLoad array (writeWord mem pos.toNat ⟨32⟩) :: _ :: _ :: _) = _
    rw [hlen']
    rfl
  rw [hs, hm] at hloop
  have hcopy := metaMorphoV1_1Blocks.metaMorphoV1_1_block_13364_taken
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega) (by decide)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hloop
  obtain ⟨_, _, _, hloop'⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_13377_packed
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by rw [metaMorphoV1_1PatchedValidJumpsRuntime v]; jump_dest) hcopy
  have hm' : metaMorphoV1_1Blocks.metaMorphoV1_1_block_13377_memory
      (mem := writeWord (writeWord mem pos.toNat ⟨32⟩) (pos + ⟨32⟩).toNat ⟨1⟩)
      (x2 := array + ⟨32⟩) (x3 := pos + ⟨64⟩) = singletonEncodeMem mem pos slot := by
    unfold metaMorphoV1_1Blocks.metaMorphoV1_1_block_13377_memory
    rw [hslot']
    rfl
  rw [hm'] at hloop'
  have hdoneLoop := metaMorphoV1_1Blocks.metaMorphoV1_1_block_13364_fallthrough
    (immWords := wordsOf (immStore v)) (by simp only [List.length_cons]; omega)
    (by decide) hloop'
  obtain ⟨aw', k', C', hdone⟩ := metaMorphoV1_1Blocks.metaMorphoV1_1_block_13372_packed
    (immWords := wordsOf (immStore v)) (by omega) hret hdoneLoop
  change RD _ _ _ _ _ ((⟨32⟩ + (pos + ⟨64⟩)) :: R) _ _ _ _ _ _ at hdone
  have hpos : ⟨32⟩ + (pos + ⟨64⟩) = pos + ⟨96⟩ := by
    rw [u256_add_comm ⟨32⟩ _, u256_add_assoc]
    rfl
  rw [hpos] at hdone
  exact ⟨aw', k', C', hdone⟩

end Benchmarks.Morpho.MetaMorphoV1_1
