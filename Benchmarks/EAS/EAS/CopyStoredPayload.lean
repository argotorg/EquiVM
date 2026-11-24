import Benchmarks.EAS.EAS.CopyStoredSource
import Benchmarks.EAS.EAS.StoredWords

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def copyStoredPayloadMemory (mem : ByteArray) (bytesPtr slot header : UInt256) (σ : AccountMap) (ee : ExecutionEnv) : ByteArray :=
  let len := storedBytesLengthWord header
  let mem' := Reasoning.Theory.writeWord mem bytesPtr.toNat len
  if UInt256.land header ⟨1⟩ = ⟨0⟩ then
    Reasoning.Theory.writeWord mem' (bytesPtr.toNat + 32) (UInt256.land (UInt256.lnot ⟨255⟩) header)
  else
    writeWordSequence (Reasoning.Theory.writeWord mem' 0 slot) (bytesPtr.toNat + 32)
      (storedWords σ ee (solidityBytesDataSlot slot 0) ((len.toNat + 31) / 32))

-- LIBRARY CANDIDATE: the byte copier's final cursor encodes its allocation size modulo 2^256.
theorem bytesCursorDifference (ptr : UInt256) (n : Nat) :
    UInt256.sub (UInt256.ofNat 32 + (ptr + UInt256.ofNat (32 * n))) ptr =
      UInt256.ofNat (32 + 32 * n) := by
  rw [u256_add_comm (UInt256.ofNat 32), u256_add_assoc, word_add_sub_left]
  exact (u256_add_comm _ _).trans (by simpa only [Nat.add_comm] using u256_32_add_ofNat (32 * n))

theorem easCopyStored_payload_cursor {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {bytesPtr ptr : UInt256} {R : List UInt256} (v : EASImmutables)
    (n : Nat) (hstack : R.length + 7 ≤ 1024)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6709⟩
      (⟨6727⟩ :: bytesPtr :: (UInt256.ofNat 32 + (bytesPtr + UInt256.ofNat (32*n))) :: bytesPtr :: ptr :: bytesPtr :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (bytesPtr :: UInt256.ofNat (32 + 32*n) :: ⟨6727⟩ :: ptr :: ⟨288⟩ :: bytesPtr :: R) mem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', rd1⟩ := easBlocks.eas_block_6709_packed (immWords := wordsOf (immStore v)) hstack
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  exact ⟨aw', k', C', by simpa only [easBlocks.eas_block_6709_stack, bytesCursorDifference] using rd1⟩

theorem easCopyStored_payload_short {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {bytesPtr ptr slot header : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 11 ≤ 1024)
    (hbound : bytesPtr.toNat + 32 < UInt256.size)
    (hf : UInt256.land header ⟨1⟩ = ⟨0⟩) (hv : storedBytesValid header)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6685⟩
      (storedBytesLengthWord header :: slot :: header :: ⟨0⟩ :: bytesPtr :: ptr :: bytesPtr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (bytesPtr :: UInt256.ofNat (bytesAllocation (storedBytesLengthWord header).toNat) :: ⟨6727⟩ :: ptr :: ⟨288⟩ :: bytesPtr :: R)
      (copyStoredPayloadMemory mem bytesPtr slot header σ ee) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_6685_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega)
    (by change UInt256.isZero (UInt256.land header ⟨1⟩) ≠ (⟨0⟩ : UInt256); rw [hf]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd
  obtain ⟨aw2, k2, C2, rd2⟩ := easBlocks.eas_block_6795_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  simp only [easBlocks.eas_block_6795_stack, shortBytesRounded _ (storedBytesValid_short hf hv)] at rd2
  obtain ⟨aw3, k3, C3, rd3⟩ := easCopyStored_payload_cursor v (((storedBytesLengthWord header).toNat + 31) / 32)
    (by omega) rd2
  refine ⟨aw3, k3, C3, ?_⟩
  have hn : (UInt256.ofNat 32 + bytesPtr).toNat = bytesPtr.toNat + 32 := by
    rw [u256_add_comm]
    exact uadd_word_ofNat_toNat _ _ hbound
  simpa only [easBlocks.eas_block_6795_memory, easBlocks.eas_block_6685_taken_memory,
    copyStoredPayloadMemory, if_pos hf, Reasoning.Theory.writeWord, hn, bytesAllocation, Nat.mul_comm] using rd3

theorem easCopyStored_payload_long {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {bytesPtr ptr slot header : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 11 ≤ 1024)
    (hbound : bytesPtr.toNat + (storedBytesLengthWord header).toNat + 64 < UInt256.size)
    (hf : UInt256.land header ⟨1⟩ ≠ ⟨0⟩)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6685⟩
      (storedBytesLengthWord header :: slot :: header :: ⟨0⟩ :: bytesPtr :: ptr :: bytesPtr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (bytesPtr :: UInt256.ofNat (bytesAllocation (storedBytesLengthWord header).toNat) :: ⟨6727⟩ :: ptr :: ⟨288⟩ :: bytesPtr :: R)
      (copyStoredPayloadMemory mem bytesPtr slot header σ ee) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, rd1⟩ := easBlocks.eas_block_6685_fallthrough_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (isZero_eq_zero_of_ne hf) rd
  have hflag : UInt256.land header (UInt256.ofNat 1) = UInt256.ofNat 1 := land_one_eq_one_of_ne_zero hf
  obtain ⟨aw2, k2, C2, rd2⟩ := easBlocks.eas_block_6701_taken_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [hflag]; decide)
    (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd1
  obtain ⟨aw3, k3, C3, rd3⟩ := easBlocks.eas_block_6731_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) rd2
  change RD fork (deployedRuntime v) ee g s0 ⟨6744⟩
    (keccakWord (UInt256.ofNat 0) (UInt256.ofNat 32)
        (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem bytesPtr.toNat (storedBytesLengthWord header)) 0 slot) ::
      storedBytesLengthWord header :: ⟨0⟩ :: bytesPtr :: ptr :: bytesPtr :: R)
    (Reasoning.Theory.writeWord (Reasoning.Theory.writeWord mem bytesPtr.toNat (storedBytesLengthWord header)) 0 slot)
    aw3 rdata σ k3 C3 at rd3
  simp only [storedBytesDataHash] at rd3
  obtain ⟨last, aw4, k4, C4, rd4⟩ := easStoredWords_loop v 0 (((storedBytesLengthWord header).toNat + 31) / 32)
    hstack (by omega) (by intro hn; omega) (by omega) rd3
  obtain ⟨aw5, k5, C5, rd5⟩ := easBlocks.eas_block_6752_packed (immWords := wordsOf (immStore v))
    (by simp only [List.length_cons]; omega) (by rw [easPatchedValidJumpsRuntime v]; jump_dest) rd4
  simp only [easBlocks.eas_block_6752_stack, Nat.zero_add] at rd5
  obtain ⟨aw6, k6, C6, rd6⟩ := easCopyStored_payload_cursor v (((storedBytesLengthWord header).toNat + 31) / 32)
    (by omega) rd5
  exact ⟨aw6, k6, C6, by simpa only [copyStoredPayloadMemory, if_neg hf, bytesAllocation, Nat.mul_comm, Nat.add_zero] using rd6⟩

theorem easCopyStored_payload {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap}
    {k C : Nat} {bytesPtr ptr slot header : UInt256} {R : List UInt256} (v : EASImmutables)
    (hstack : R.length + 11 ≤ 1024)
    (hbound : bytesPtr.toNat + (storedBytesLengthWord header).toNat + 64 < UInt256.size)
    (hv : storedBytesValid header)
    (rd : RD fork (deployedRuntime v) ee g s0 ⟨6685⟩
      (storedBytesLengthWord header :: slot :: header :: ⟨0⟩ :: bytesPtr :: ptr :: bytesPtr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', RD fork (deployedRuntime v) ee g s0 ⟨4883⟩
      (bytesPtr :: UInt256.ofNat (bytesAllocation (storedBytesLengthWord header).toNat) :: ⟨6727⟩ :: ptr :: ⟨288⟩ :: bytesPtr :: R)
      (copyStoredPayloadMemory mem bytesPtr slot header σ ee) aw' rdata σ k' C' := by
  by_cases hf : UInt256.land header ⟨1⟩ = ⟨0⟩
  · exact easCopyStored_payload_short v hstack (by omega) hf hv rd
  · exact easCopyStored_payload_long v hstack hbound hf rd

end Benchmarks.EAS.EAS
