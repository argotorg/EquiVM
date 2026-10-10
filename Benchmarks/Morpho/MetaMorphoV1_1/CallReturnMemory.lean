import Benchmarks.Morpho.MetaMorphoV1_1.AllocationSource
import Reasoning.HeapMemory
import Benchmarks.EAS.Attester.Memory
import Benchmarks.EAS.Attester.WordHelpers

/-! Exact memory for a nonempty raw-call return buffer. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

theorem nextCursor_bytesAlloc (ptr : UInt256) (size : Nat) :
    nextCursor ptr (UInt256.ofNat (32 + size)) = bytesAllocPtr ptr size := by
  unfold nextCursor roundedSize bytesAllocPtr bytesAllocSize
  rw [u256_land_comm]
  change ptr + UInt256.land _ (UInt256.ofNat (32 + size) + UInt256.ofNat 31) =
    ptr + UInt256.land _ (UInt256.ofNat size + UInt256.ofNat 63)
  rw [ofNat_add_words, ofNat_add_words]
  congr 2
  congr 1
  omega

def callReturnFits (ptr : UInt256) (out : ByteArray) : Prop :=
  out.size = 0 ∨ (out.size < 2 ^ 64 ∧ allocationFits ptr (UInt256.ofNat (32 + out.size)))

instance (ptr : UInt256) (out : ByteArray) : Decidable (callReturnFits ptr out) :=
  inferInstanceAs (Decidable (_ ∨ _))

def callReturnCursor (ptr : UInt256) (out : ByteArray) : UInt256 :=
  if out.size = 0 then ptr else bytesAllocPtr ptr out.size

def callReturnPointer (ptr : UInt256) (out : ByteArray) : UInt256 :=
  if out.size = 0 then ⟨96⟩ else ptr

def callReturnMemory (mem : ByteArray) (ptr : UInt256) (out : ByteArray) : ByteArray :=
  if out.size = 0 then mem else bytesAllocMem mem out ptr

-- GENERALIZES bytesAlloc_prefix by removing unrelated active-memory hypotheses.
theorem bytesAllocMem_prefix (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hpos : out.size ≠ 0) : MemoryPrefix mem (bytesAllocMem mem out ptr) ptr.toNat := by
  exact (memoryPrefix_sparse_writeWord mem 64 ptr.toNat _ (.inr (by decide))).trans
    ((memoryPrefix_sparse_writeWord _ ptr.toNat ptr.toNat _ (.inl (le_refl _))).trans
      (memoryPrefix_writeBytes out _ (ptr.toNat + 32) ptr.toNat hpos
        (by simp only [writeWord_sparse_size]; omega) (by omega)))

theorem bytesAllocMem_size (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hpos : out.size ≠ 0) :
    (bytesAllocMem mem out ptr).size = max (max mem.size 96) (ptr.toNat + 32 + out.size) := by
  rw [bytesAllocMem, writeBytes_size _ _ _ hpos
    (by simp only [writeWord_sparse_size]; omega)]
  simp only [writeWord_sparse_size]
  omega

theorem bytesAllocMem_length (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hpos : out.size ≠ 0) :
    memLoad ptr (bytesAllocMem mem out ptr) = UInt256.ofNat out.size := by
  apply mloadWordValue_of_readWithPadding
  · rw [bytesAllocMem_size mem ptr out hpos]
    omega
  · unfold bytesAllocMem
    rw [write_read_below_gen_extend out _ (ptr.toNat + 32) out.size ptr.toNat hpos
      (le_refl _) (by simp only [writeWord_sparse_size]; omega) (by omega)]
    exact writeWord_sparse_read_back _ _ _

theorem bytesAllocMem_free (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hpos : out.size ≠ 0) (hlo : 96 ≤ ptr.toNat) :
    memLoad ⟨64⟩ (bytesAllocMem mem out ptr) = bytesAllocPtr ptr out.size := by
  apply mloadWordValue_of_readWithPadding
  · rw [bytesAllocMem_size mem ptr out hpos]
    change 64 < _
    omega
  · unfold bytesAllocMem
    change (out.write 0 _ (ptr.toNat + 32) out.size).readWithPadding 64 32 = _
    rw [write_read_below_gen_extend out _ (ptr.toNat + 32) out.size 64 hpos
      (le_refl _) (by simp only [writeWord_sparse_size]; omega) (by omega)]
    rw [writeWord_sparse_read_preserved _ ptr.toNat 64 _
      (.inl ⟨hlo, by rw [writeWord_sparse_size]; omega⟩)]
    exact writeWord_sparse_read_back _ _ _

theorem bytesAllocMem_word (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hl : 32 ≤ out.size) (hptr : ptr.toNat + 32 < UInt256.size) :
    memLoad (ptr + ⟨32⟩) (bytesAllocMem mem out ptr) = calldataWord out 0 := by
  have hs := bytesAllocMem_size mem ptr out (by omega)
  have hp : (ptr + (⟨32⟩ : UInt256)).toNat = ptr.toNat + 32 :=
    uadd_word_ofNat_toNat ptr 32 hptr
  unfold memLoad
  rw [if_neg (by rw [hp]; omega)]
  unfold bytesAllocMem
  rw [hp]
  have hr := copyWindow_read_word out
    (writeWord (writeWord mem 64 (bytesAllocPtr ptr out.size)) ptr.toNat
      (UInt256.ofNat out.size)) 0 (ptr.toNat + 32) out.size 0 (by omega)
      (by omega) (by simp only [writeWord_sparse_size]; omega) (by omega)
  simp only [Nat.add_zero] at hr
  rw [hr]
  rw [readWithPadding_eq_extract _ _ (by omega), ← calldataWord_bytes hl,
    fromByteArrayBigEndian_toByteArray, u256_ofNat_toNat]

theorem callReturnMemory_prefix (mem : ByteArray) (ptr : UInt256) (out : ByteArray) :
    MemoryPrefix mem (callReturnMemory mem ptr out) ptr.toNat := by
  unfold callReturnMemory
  split
  · exact .refl _ _
  · exact bytesAllocMem_prefix mem ptr out ‹_›

theorem callReturnMemory_length (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hzero : memLoad ⟨96⟩ mem = ⟨0⟩) :
    memLoad (callReturnPointer ptr out) (callReturnMemory mem ptr out) =
      UInt256.ofNat out.size := by
  unfold callReturnPointer callReturnMemory
  split
  · simpa only [‹out.size = 0›] using hzero
  · exact bytesAllocMem_length mem ptr out ‹_›

theorem callReturnMemory_free (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hlo : 96 ≤ ptr.toNat) (hfree : memLoad ⟨64⟩ mem = ptr) :
    memLoad ⟨64⟩ (callReturnMemory mem ptr out) = callReturnCursor ptr out := by
  unfold callReturnMemory callReturnCursor
  split
  · exact hfree
  · exact bytesAllocMem_free mem ptr out ‹_› hlo

theorem callReturnMemory_word (mem : ByteArray) (ptr : UInt256) (out : ByteArray)
    (hl : 32 ≤ out.size) (hptr : ptr.toNat + 32 < UInt256.size) :
    memLoad (callReturnPointer ptr out + ⟨32⟩) (callReturnMemory mem ptr out) =
      calldataWord out 0 := by
  simp only [callReturnMemory, callReturnPointer, if_neg (by omega : out.size ≠ 0)]
  exact bytesAllocMem_word mem ptr out hl hptr

theorem callReturnCursor_bound (ptr : UInt256) (out : ByteArray)
    (hp : ptr.toNat < 2 ^ 64) (hfit : callReturnFits ptr out) :
    (callReturnCursor ptr out).toNat < 2 ^ 64 ∧ ptr.toNat ≤ (callReturnCursor ptr out).toNat := by
  unfold callReturnCursor
  split
  · exact ⟨hp, le_refl _⟩
  · have ha := (hfit.resolve_left ‹out.size ≠ 0›).2
    rwa [allocationFits, nextCursor_bytesAlloc] at ha

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
