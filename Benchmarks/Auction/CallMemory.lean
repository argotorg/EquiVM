import Benchmarks.Auction.HeapMemory
import Benchmarks.Auction.Memory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def depositWord : UInt256 := ⟨0xd0e30db0 * 2 ^ 224⟩
def transferWord : UInt256 := ⟨0xa9059cbb * 2 ^ 224⟩

theorem depositWord_prefix : depositWord.toByteArray.extract 0 4 = depositSelector := by
  native_decide

theorem transferWord_prefix : transferWord.toByteArray.extract 0 4 = transferSelector := by
  native_decide

noncomputable def selectorMem (mem : ByteArray) (ptr selector : UInt256) : ByteArray :=
  writeWord mem ptr.toNat selector

theorem selectorMem_read {mem aw ptr} (h : HeapMemory mem aw ptr) (selector : UInt256) :
    (selectorMem mem ptr selector).readWithPadding ptr.toNat 4 =
      selector.toByteArray.extract 0 4 := by
  exact writeWord_read_window mem ptr.toNat 0 4 selector (by decide) (by decide)
    (by decide) (by have hu := lt_usize 32 (by decide); have hg := h.gap; omega)

theorem selectorMem_heap {mem aw ptr} (h : HeapMemory mem aw ptr) (selector : UInt256)
    (hb : ptr.toNat + 32 ≤ 2 ^ 200) :
    HeapMemory (selectorMem mem ptr selector) (expandedWords aw ptr ⟨32⟩) ptr :=
  h.writeAbove ptr selector (le_refl _) h.gap hb

theorem selectorMem_prefix {mem aw ptr} (h : HeapMemory mem aw ptr) (selector : UInt256) :
    MemoryPrefix mem (selectorMem mem ptr selector) ptr.toNat :=
  memoryPrefix_writeWord mem ptr.toNat ptr.toNat selector
    (by have hu := lt_usize 32 (by decide); have hg := h.gap; omega) (Or.inl (le_refl _))

noncomputable def callMem2 (mem : ByteArray) (ptr selector arg1 arg2 : UInt256) : ByteArray :=
  writeWord (writeWord (selectorMem mem ptr selector) (ptr.toNat + 4) arg1)
    (ptr.toNat + 36) arg2

def callWords2 (aw ptr : UInt256) : UInt256 :=
  expandedWords (expandedWords (expandedWords aw ptr ⟨32⟩) (ptr + ⟨4⟩) ⟨32⟩)
    (ptr + ⟨36⟩) ⟨32⟩

theorem callMem2_sizes {mem aw ptr} (h : HeapMemory mem aw ptr) (selector arg1 arg2 : UInt256) :
    (selectorMem mem ptr selector).size = max mem.size (ptr.toNat + 32) ∧
    (writeWord (selectorMem mem ptr selector) (ptr.toNat + 4) arg1).size =
      max mem.size (ptr.toNat + 36) ∧
    (callMem2 mem ptr selector arg1 arg2).size = max mem.size (ptr.toNat + 68) := by
  have hg : ptr.toNat - mem.size < USize.size := by
    have hu := lt_usize 32 (by decide)
    have hp := h.gap
    omega
  have hs0 := writeWord_size mem ptr.toNat selector hg
  change (selectorMem mem ptr selector).size = _ at hs0
  have hs1 := writeWord_size (selectorMem mem ptr selector) (ptr.toNat + 4) arg1
    (by have hu := lt_usize 0 (by decide); omega)
  have hs2 := writeWord_size (writeWord (selectorMem mem ptr selector) (ptr.toNat + 4) arg1)
    (ptr.toNat + 36) arg2 (by have hu := lt_usize 0 (by decide); omega)
  exact ⟨hs0, by omega, by change (Reasoning.Theory.writeWord _ _ _).size = _; omega⟩

theorem callMem2_heap {mem aw ptr} (h : HeapMemory mem aw ptr) (selector arg1 arg2 : UInt256)
    (hb : ptr.toNat + 68 ≤ 2 ^ 200) :
    HeapMemory (callMem2 mem ptr selector arg1 arg2) (callWords2 aw ptr) ptr := by
  obtain ⟨hs0, hs1, _⟩ := callMem2_sizes h selector arg1 arg2
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 :=
    addWord_toNat ptr ⟨4⟩ (by change ptr.toNat + 4 < 2 ^ 256; omega)
  have h36 : (ptr + ⟨36⟩).toNat = ptr.toNat + 36 :=
    addWord_toNat ptr ⟨36⟩ (by change ptr.toNat + 36 < 2 ^ 256; omega)
  have h0 := selectorMem_heap h selector (by omega)
  have h1 := h0.writeAbove (ptr + ⟨4⟩) arg1 (by omega) (by omega) (by omega)
  rw [h4] at h1
  have h2 := h1.writeAbove (ptr + ⟨36⟩) arg2 (by omega) (by omega) (by omega)
  rw [h36] at h2
  exact h2

theorem callMem2_prefix {mem aw ptr} (h : HeapMemory mem aw ptr)
    (selector arg1 arg2 : UInt256) :
    MemoryPrefix mem (callMem2 mem ptr selector arg1 arg2) ptr.toNat := by
  obtain ⟨hs0, hs1, _⟩ := callMem2_sizes h selector arg1 arg2
  exact (selectorMem_prefix h selector).trans
    ((memoryPrefix_writeWord _ (ptr.toNat + 4) ptr.toNat arg1
      (by have hu := lt_usize 0 (by decide); omega) (Or.inl (by omega))).trans
      (memoryPrefix_writeWord _ (ptr.toNat + 36) ptr.toNat arg2
        (by have hu := lt_usize 0 (by decide); omega) (Or.inl (by omega))))

theorem callMem2_read {mem aw ptr} (h : HeapMemory mem aw ptr)
    (selector arg1 arg2 : UInt256) :
    (callMem2 mem ptr selector arg1 arg2).readWithPadding ptr.toNat 68 =
      selector.toByteArray.extract 0 4 ++ arg1.toByteArray ++ arg2.toByteArray := by
  obtain ⟨hs0, hs1, hs2⟩ := callMem2_sizes h selector arg1 arg2
  have hg1 : ptr.toNat + 4 - (selectorMem mem ptr selector).size < USize.size := by
    have hu := lt_usize 0 (by decide)
    omega
  have hg2 : ptr.toNat + 36 -
      (writeWord (selectorMem mem ptr selector) (ptr.toNat + 4) arg1).size < USize.size := by
    have hu := lt_usize 0 (by decide)
    omega
  have hr0 : (callMem2 mem ptr selector arg1 arg2).readWithPadding ptr.toNat 4 =
      selector.toByteArray.extract 0 4 := by
    unfold callMem2
    rw [writeWord_read_preserved_len _ (ptr.toNat + 36) ptr.toNat 4 arg2 hg2
      (Or.inl ⟨by omega, by omega⟩) (by decide) (by decide)]
    rw [writeWord_read_preserved_len _ (ptr.toNat + 4) ptr.toNat 4 arg1 hg1
      (Or.inl ⟨by omega, by omega⟩) (by decide) (by decide), selectorMem_read h selector]
  have hr1 : (callMem2 mem ptr selector arg1 arg2).readWithPadding (ptr.toNat + 4) 32 =
      arg1.toByteArray := by
    unfold callMem2
    rw [writeWord_read_preserved _ (ptr.toNat + 36) (ptr.toNat + 4) arg2 hg2
      (Or.inl ⟨by omega, by omega⟩), writeWord_read_back _ (ptr.toNat + 4) arg1 hg1]
  have hr2 : (callMem2 mem ptr selector arg1 arg2).readWithPadding (ptr.toNat + 36) 32 =
      arg2.toByteArray := writeWord_read_back _ (ptr.toNat + 36) arg2 hg2
  rw [show 68 = 4 + 64 from rfl,
    byteArray_readWithPadding_split _ ptr.toNat 4 64 (by decide) (by decide) (by decide)
      (by decide) (by decide) (by omega),
    byteArray_readWithPadding_split _ (ptr.toNat + 4) 32 32 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by omega)]
  rw [hr0, hr1, show ptr.toNat + 4 + 32 = ptr.toNat + 36 by omega, hr2,
    ByteArray.append_assoc]

end Auction
