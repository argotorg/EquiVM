import Benchmarks.EAS.EAS.FixedAllocate
import Benchmarks.EAS.EAS.RuntimeBlocks_025
import Benchmarks.EAS.EAS.WordSequence

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem allocate320_word (heap : UInt256) :
    heap + UInt256.ofNat 320 = UInt256.ofNat (allocateNext heap.toNat 320) :=
  fixedAllocation_word .bytes320 heap

theorem easAllocate320_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 5 ≤ 1024)
    (hguard : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4854⟩ (heap :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret R
      (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320))) aw' rdata σ k' C' :=
  easFixedAllocate_ok v .bytes320 hstack hguard hvalid rd

theorem easAllocate320_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 4 ≤ 1024)
    (hguard : ¬ (allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨4854⟩ (heap :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 :=
  easFixedAllocate_revert v .bytes320 hstack hguard rd

theorem allocate320_bounds {heap : Nat}
    (hg : allocateNext heap 320 ≤ 2^64-1 ∧ heap ≤ allocateNext heap 320) :
    allocateNext heap 320 = heap + 320 ∧ heap + 320 ≤ 2^64-1 := by
  have hb : heap ≤ 2^64-1 := le_trans hg.2 hg.1
  have hn : allocateNext heap 320 = heap+320 := fixedAllocation_next .bytes320 hb
  exact ⟨hn, hn ▸ hg.1⟩

def defaultAttestationWords : List UInt256 := [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨96⟩]

def defaultAttestationMemory (mem : ByteArray) (heap : UInt256) : ByteArray :=
  writeWordSequence (Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320)))
    heap.toNat defaultAttestationWords

theorem defaultAttestationMemory_eq (mem : ByteArray) (heap : UInt256)
    (hb : heap.toNat + 320 < UInt256.size) :
    easBlocks.eas_block_6348_memory
      (mem := Reasoning.Theory.writeWord mem 64 (UInt256.ofNat (allocateNext heap.toNat 320))) (x1 := heap) =
      defaultAttestationMemory mem heap := by
  have hn : ∀ n, n ≤ 320 → (heap + UInt256.ofNat n).toNat = heap.toNat + n :=
    fun n hn => uadd_word_ofNat_toNat heap n (by omega)
  simp only [easBlocks.eas_block_6348_memory, defaultAttestationMemory, defaultAttestationWords,
    writeWordSequence, Reasoning.Theory.writeWord,
    hn 32 (by decide), hn 64 (by decide), hn 96 (by decide), hn 128 (by decide),
    hn 160 (by decide), hn 192 (by decide), hn 224 (by decide), hn 256 (by decide), hn 288 (by decide), Nat.add_assoc]
  rfl

theorem defaultAttestationMemory_heap (mem : ByteArray) (heap : UInt256) (hlo : 96 ≤ heap.toNat) :
    memLoad ⟨64⟩ (defaultAttestationMemory mem heap) = UInt256.ofNat (allocateNext heap.toNat 320) :=
  writeWordSequence_setFree_load64 mem heap.toNat defaultAttestationWords _ hlo

theorem easDefaultAttestation_ok {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 8 ≤ 1024)
    (hh : memLoad ⟨64⟩ mem = heap)
    (hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6335⟩ (ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ret (heap :: R)
      (defaultAttestationMemory mem heap) aw' rdata σ k' C' := by
  have rd1 := easBlocks.eas_block_6335 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  change memLoad (UInt256.ofNat 64) mem = heap at hh
  simp only [easBlocks.eas_block_6335_stack, hh] at rd1
  obtain ⟨aw1, k1, C1, rd2⟩ := easAllocate320_ok v (by simp only [List.length_cons]; omega) hg
    (by rw [easPatchedValidJumps v]; jump_dest) rd1
  obtain ⟨aw2, k2, C2, rd3⟩ := easBlocks.eas_block_6348_packed (immWords := wordsOf (immStore v)) hstack hvalid rd2
  refine ⟨aw2, k2, C2, ?_⟩
  simpa only [easBlocks.eas_block_6348_stack, defaultAttestationMemory_eq mem heap
    (by have hb := (allocate320_bounds hg).2; change heap.toNat + 320 < 2^256; omega)] using rd3

theorem easDefaultAttestation_revert {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {heap ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 7 ≤ 1024)
    (hh : memLoad ⟨64⟩ mem = heap)
    (hg : ¬ (allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320))
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6335⟩ (ret :: R) mem aw rdata σ k C) :
    RDrev fork (deployedRuntime v) g s0 := by
  have rd1 := easBlocks.eas_block_6335 (immWords := wordsOf (immStore v)) (by omega)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  change memLoad (UInt256.ofNat 64) mem = heap at hh
  simp only [easBlocks.eas_block_6335_stack, hh] at rd1
  exact easAllocate320_revert v (by simp only [List.length_cons]; omega) hg rd1

end Benchmarks.EAS.EAS
