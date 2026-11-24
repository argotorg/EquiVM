import Benchmarks.EAS.EAS.StructAllocate
import Benchmarks.EAS.EAS.BytesLength

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def storedAttestationWords (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) : List UInt256 := [
  solcSlotWord σ ee slot, solcSlotWord σ ee (slot + ⟨1⟩),
  UInt256.land (solcSlotWord σ ee (slot + ⟨2⟩)) ⟨18446744073709551615⟩,
  UInt256.land (UInt256.shiftRight (solcSlotWord σ ee (slot + ⟨2⟩)) ⟨64⟩) ⟨18446744073709551615⟩,
  UInt256.land (UInt256.shiftRight (solcSlotWord σ ee (slot + ⟨2⟩)) ⟨128⟩) ⟨18446744073709551615⟩,
  solcSlotWord σ ee (slot + ⟨3⟩),
  UInt256.land (solcSlotWord σ ee (slot + ⟨4⟩)) ⟨1461501637330902918203684832716283019655932542975⟩,
  UInt256.land (solcSlotWord σ ee (slot + ⟨5⟩)) ⟨1461501637330902918203684832716283019655932542975⟩,
  UInt256.isZero (UInt256.isZero (UInt256.land (UInt256.shiftRight (solcSlotWord σ ee (slot + ⟨5⟩)) ⟨160⟩) ⟨255⟩))]

def copyStoredFieldsMemory (mem : ByteArray) (heap : UInt256) (σ : AccountMap) (ee : ExecutionEnv) (slot : UInt256) : ByteArray :=
  writeWordSequence (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320)))
    heap.toNat (storedAttestationWords σ ee slot)

theorem copyStoredFieldsMemory_eq (mem : ByteArray) (heap slot : UInt256) (σ : AccountMap) (ee : ExecutionEnv)
    (hb : heap.toNat + 320 < UInt256.size) :
    easBlocks.eas_block_6621_memory (ee := ee) (σ := σ) (x0 := UInt256.ofNat 5) (x1 := UInt256.ofNat 255) (x2 := slot) (x4 := heap)
      (mem := easBlocks.eas_block_6514_memory (ee := ee) (σ := σ) (x0 := heap) (x2 := slot)
        (mem := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320)))) =
      copyStoredFieldsMemory mem heap σ ee slot := by
  have hn : ∀ n, n ≤ 320 → (heap + UInt256.ofNat n).toNat = heap.toNat + n :=
    fun n hn => uadd_word_ofNat_toNat heap n (by omega)
  simp only [easBlocks.eas_block_6621_memory, easBlocks.eas_block_6514_memory,
    copyStoredFieldsMemory, storedAttestationWords, writeWordSequence, Reasoning.Theory.writeWord,
    hn 32 (by decide), hn 64 (by decide), hn 96 (by decide), hn 128 (by decide),
    hn 160 (by decide), hn 192 (by decide), hn 224 (by decide), hn 256 (by decide), Nat.add_assoc]
  rfl

theorem copyStoredFieldsMemory_heap (mem : ByteArray) (heap slot : UInt256) (σ : AccountMap) (ee : ExecutionEnv)
    (hlo : 96 ≤ heap.toNat) :
    memLoad (UInt256.ofNat 64) (copyStoredFieldsMemory mem heap σ ee slot) = UInt256.ofNat (allocateNext heap.toNat 320) :=
  writeWordSequence_setFree_load64 mem heap.toNat (storedAttestationWords σ ee slot) _ hlo

theorem easCopyStored_fields {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap slot ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 11 ≤ 1024)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hlo : 96 ≤ heap.toNat)
    (hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6501⟩ (slot :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨6418⟩
      (solcSlotWord σ ee (slot + ⟨6⟩) :: ⟨6685⟩ :: (slot + ⟨6⟩) :: solcSlotWord σ ee (slot + ⟨6⟩) :: ⟨0⟩ ::
        UInt256.ofNat (allocateNext heap.toNat 320) :: heap :: UInt256.ofNat (allocateNext heap.toNat 320) :: ret :: heap :: R)
      (copyStoredFieldsMemory mem heap σ ee slot) aw' rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_6501 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_6501_stack, hh] at rd1
  obtain ⟨aw1, k1, C1, rd2⟩ := easAllocate320_ok v (by simp only [List.length_cons]; omega) hg
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  obtain ⟨aw2, k2, C2, rd3⟩ := easBlocks.eas_block_6514_packed (immWords := wordsOf (immStore v)) (by omega) rd2
  simp only [easBlocks.eas_block_6514_stack] at rd3
  obtain ⟨aw3, k3, C3, rd4⟩ := easBlocks.eas_block_6621_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd3
  have hm := copyStoredFieldsMemory_eq mem heap slot σ ee
    (by have hb := (allocate320_bounds hg).2; change heap.toNat + 320 < 2^256; omega)
  change RD fork (deployedRuntime v) ee g s0 ⟨6418⟩
    (solcSlotWord σ ee (slot + ⟨6⟩) :: ⟨6685⟩ :: (slot + ⟨6⟩) :: solcSlotWord σ ee (slot + ⟨6⟩) :: ⟨0⟩ ::
      memLoad (UInt256.ofNat 64) _ :: heap :: memLoad (UInt256.ofNat 64) _ :: ret :: heap :: R) _ aw3 rdata σ k3 C3 at rd4
  have hmExpanded := hm
  dsimp only [easBlocks.eas_block_6621_memory] at hmExpanded
  simp only [hm, hmExpanded, copyStoredFieldsMemory_heap mem heap slot σ ee hlo] at rd4
  exact ⟨aw3, k3, C3, rd4⟩

theorem easCopyStored_revert_allocate {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap slot ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024)
    (hh : memLoad (UInt256.ofNat 64) mem = heap)
    (hg : ¬ (allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6501⟩ (slot :: ret :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have rd1 := easBlocks.eas_block_6501 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [easBlocks.eas_block_6501_stack, hh] at rd1
  exact easAllocate320_revert v (by simp only [List.length_cons]; omega) hg rd1

end Benchmarks.EAS.EAS
