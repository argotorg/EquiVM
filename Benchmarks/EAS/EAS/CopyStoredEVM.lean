import Benchmarks.EAS.EAS.CopyStoredFields
import Benchmarks.EAS.EAS.CopyStoredPayload

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: a byte allocation with an in-range storage length cannot wrap its size word.
theorem bytesAllocation_lt {len : Nat} (hl : len < 2^255) : bytesAllocation len + 31 < UInt256.size := by
  unfold bytesAllocation
  change 32 + (len + 31) / 32 * 32 + 31 < 2^256
  omega

theorem attestationPayload_size (evm : EVM.State) (word : UInt256) :
    (attestationPayload evm word).size = (storedBytesLengthWord (attestationHeader evm word)).toNat :=
  storedBytesPayload_size _ _ _

def copyStoredBytePtr (heap : UInt256) : UInt256 := UInt256.ofNat (allocateNext heap.toNat 320)

def copyStoredOutputMemory (evm : EVM.State) (word heap : UInt256) (mem : ByteArray) : ByteArray :=
  Reasoning.Theory.writeWord
    (Reasoning.Theory.writeWord
      (copyStoredPayloadMemory (copyStoredFieldsMemory mem heap evm.accountMap evm.executionEnv (dbSlot word))
        (copyStoredBytePtr heap) (dbSlot word + ⟨6⟩) (attestationHeader evm word) evm.accountMap evm.executionEnv)
      64 (UInt256.ofNat (copyStoredNext heap.toNat (attestationPayload evm word))))
    (heap.toNat + 288) (copyStoredBytePtr heap)

theorem easCopyStored {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {k C : Nat} {heap word ret : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 13 ≤ 1024)
    (hh : memLoad (UInt256.ofNat 64) mem = heap) (hlo : 96 ≤ heap.toNat)
    (hvalid : (D_J (deployedRuntime v) 0).contains ret = true)
    (rd : RD fork (deployedRuntime v) evm.executionEnv g s0 ⟨6501⟩ (dbSlot word :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    if copyStoredValid evm word heap.toNat then
      ∃ aw' k' C', RD fork (deployedRuntime v) evm.executionEnv g s0 ret (heap :: R)
        (copyStoredOutputMemory evm word heap mem) aw' rdata evm.accountMap k' C'
    else RDrev fork (deployedRuntime v) g s0 := by
  by_cases hg : allocateNext heap.toNat 320 ≤ 2^64-1 ∧ heap.toNat ≤ allocateNext heap.toNat 320
  · obtain ⟨aw1, k1, C1, rd1⟩ := easCopyStored_fields v (by omega) hh hlo hg rd
    have hd : solcSlotWord evm.accountMap evm.executionEnv (dbSlot word + ⟨6⟩) = attestationHeader evm word :=
      (storageLoad_eq_solcSlotWord evm evm.executionEnv _).symm
    simp only [hd] at rd1
    have rdl := easStoredLength v (by simp only [List.length_cons]; omega)
      (by rw [easPatchedValidJumps v]; jump_dest) rd1
    by_cases hv : storedBytesValid (attestationHeader evm word)
    · rw [if_pos hv] at rdl
      obtain ⟨k2, C2, rd2⟩ := rdl
      have hbn : (copyStoredBytePtr heap).toNat = allocateNext heap.toNat 320 :=
        ulit_toNat' _ (by have hb := hg.1; change allocateNext heap.toNat 320 < 2^256; omega)
      have hlen := storedBytesLength_bound (attestationHeader evm word)
      have has : (UInt256.ofNat (bytesAllocation (storedBytesLengthWord (attestationHeader evm word)).toNat)).toNat =
          bytesAllocation (storedBytesLengthWord (attestationHeader evm word)).toNat :=
        ulit_toNat' _ (by have h := bytesAllocation_lt hlen; omega)
      have hfit : (copyStoredBytePtr heap).toNat + (storedBytesLengthWord (attestationHeader evm word)).toNat + 64 < UInt256.size := by
        rw [hbn]
        have hb := hg.1
        change allocateNext heap.toNat 320 + (storedBytesLengthWord (attestationHeader evm word)).toNat + 64 < 2^256
        omega
      obtain ⟨aw3, k3, C3, rd3⟩ := easCopyStored_payload v (by simp only [List.length_cons]; omega) hfit hv rd2
      have hnext : allocateNext (copyStoredBytePtr heap).toNat
          (UInt256.ofNat (bytesAllocation (storedBytesLengthWord (attestationHeader evm word)).toNat)).toNat =
          copyStoredNext heap.toNat (attestationPayload evm word) := by
        rw [hbn, has, copyStoredNext, attestationPayload_size]
      dsimp only [copyStoredBytePtr] at hbn hnext
      by_cases hb : copyStoredNext heap.toNat (attestationPayload evm word) ≤ 2^64-1 ∧
          allocateNext heap.toNat 320 ≤ copyStoredNext heap.toNat (attestationPayload evm word)
      · have hc : copyStoredValid evm word heap.toNat := ⟨hg, hv, hb⟩
        rw [if_pos hc]
        obtain ⟨aw4, k4, C4, rd4⟩ := easAllocate_ok v (by simp only [List.length_cons]; omega)
          (by simpa only [copyStoredBytePtr, copyStoredNext, attestationPayload_size, hbn, has] using hb) (by rw [easPatchedValidJumps v]; jump_dest) rd3
        obtain ⟨aw5, k5, C5, rd5⟩ := easBlocks.eas_block_6727_packed (immWords := wordsOf (immStore v))
          (by simp only [List.length_cons]; omega) hvalid rd4
        have hm : (heap + (⟨288⟩ : UInt256)).toNat = heap.toNat + 288 :=
          uadd_word_ofNat_toNat _ _ (by have hl := (allocate320_bounds hg).2; change heap.toNat + 288 < 2^256; omega)
        refine ⟨aw5, k5, C5, ?_⟩
        simp only [easBlocks.eas_block_6727_stack, easBlocks.eas_block_6727_memory, hm,
          copyStoredOutputMemory, copyStoredBytePtr, hnext, Reasoning.Theory.writeWord] at rd5 ⊢
        exact rd5
      · have hc : ¬ copyStoredValid evm word heap.toNat := fun h => hb h.2.2
        rw [if_neg hc]
        exact easAllocate_revert v (by simp only [List.length_cons]; omega)
          (by simpa only [copyStoredBytePtr, copyStoredNext, attestationPayload_size, hbn, has] using hb) rd3
    · have hc : ¬ copyStoredValid evm word heap.toNat := fun h => hv h.2.1
      rw [if_neg hc]
      simpa only [if_neg hv] using rdl
  · have hc : ¬ copyStoredValid evm word heap.toNat := fun h => hg h.1
    rw [if_neg hc]
    exact easCopyStored_revert_allocate v (by omega) hh hg rd

end Benchmarks.EAS.EAS
