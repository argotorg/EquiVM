import Benchmarks.Auction.CallMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

def burnWord : UInt256 := ⟨0x42966c68 * 2 ^ 224⟩
def transferFromWord : UInt256 := ⟨0x23b872dd * 2 ^ 224⟩

theorem burnWord_prefix : burnWord.toByteArray.extract 0 4 = burnSelector := by native_decide
theorem transferFromWord_prefix : transferFromWord.toByteArray.extract 0 4 =
  transferFromSelector := by
  native_decide

noncomputable def callMem1 (mem : ByteArray) (ptr selector arg : UInt256) : ByteArray :=
  writeWord (selectorMem mem ptr selector) (ptr.toNat + 4) arg

def callWords1 (aw ptr : UInt256) : UInt256 :=
  expandedWords (expandedWords aw ptr ⟨32⟩) (ptr + ⟨4⟩) ⟨32⟩

theorem callMem1_size {mem aw ptr} (h : HeapMemory mem aw ptr) (selector arg : UInt256) :
    (callMem1 mem ptr selector arg).size = max mem.size (ptr.toNat + 36) :=
  (callMem2_sizes h selector arg ⟨0⟩).2.1

theorem callMem1_heap {mem aw ptr} (h : HeapMemory mem aw ptr) (selector arg : UInt256)
    (hb : ptr.toNat + 36 ≤ 2 ^ 200) :
    HeapMemory (callMem1 mem ptr selector arg) (callWords1 aw ptr) ptr := by
  have hs := (callMem2_sizes h selector arg ⟨0⟩).1
  have h4 : (ptr + ⟨4⟩).toNat = ptr.toNat + 4 :=
    addWord_toNat ptr ⟨4⟩ (by change ptr.toNat + 4 < 2 ^ 256; omega)
  have hh := (selectorMem_heap h selector (by omega)).writeAbove (ptr + ⟨4⟩) arg
    (by omega) (by omega) (by omega)
  simpa only [h4] using hh

theorem callMem1_prefix {mem aw ptr} (h : HeapMemory mem aw ptr) (selector arg : UInt256) :
    MemoryPrefix mem (callMem1 mem ptr selector arg) ptr.toNat := by
  have hs := (callMem2_sizes h selector arg ⟨0⟩).1
  exact (selectorMem_prefix h selector).trans
    (memoryPrefix_writeWord _ (ptr.toNat + 4) ptr.toNat arg
      (by have hu := lt_usize 0 (by decide); omega) (Or.inl (by omega)))

theorem callMem1_read {mem aw ptr} (h : HeapMemory mem aw ptr) (selector arg : UInt256) :
    (callMem1 mem ptr selector arg).readWithPadding ptr.toNat 36 =
      selector.toByteArray.extract 0 4 ++ arg.toByteArray := by
  have hs0 := (callMem2_sizes h selector arg ⟨0⟩).1
  have hs1 := callMem1_size h selector arg
  have hg : ptr.toNat + 4 - (selectorMem mem ptr selector).size < USize.size := by
    have hu := lt_usize 0 (by decide)
    omega
  rw [show 36 = 4 + 32 from rfl, byteArray_readWithPadding_split _ ptr.toNat 4 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  unfold callMem1
  rw [writeWord_read_preserved_len _ (ptr.toNat + 4) ptr.toNat 4 arg hg
      (Or.inl ⟨by omega, by omega⟩) (by decide) (by decide),
    selectorMem_read h selector, writeWord_read_back _ (ptr.toNat + 4) arg hg]

noncomputable def callMem3 (mem : ByteArray) (ptr selector arg1 arg2 arg3 : UInt256) : ByteArray :=
  writeWord (callMem2 mem ptr selector arg1 arg2) (ptr.toNat + 68) arg3

def callWords3 (aw ptr : UInt256) : UInt256 :=
  expandedWords (callWords2 aw ptr) (ptr + ⟨68⟩) ⟨32⟩

theorem callMem3_size {mem aw ptr} (h : HeapMemory mem aw ptr)
    (selector arg1 arg2 arg3 : UInt256) :
    (callMem3 mem ptr selector arg1 arg2 arg3).size = max mem.size (ptr.toNat + 100) := by
  have hs := (callMem2_sizes h selector arg1 arg2).2.2
  unfold callMem3
  rw [writeWord_size _ _ _ (by have hu := lt_usize 0 (by decide); omega), hs]
  omega

theorem callMem3_heap {mem aw ptr} (h : HeapMemory mem aw ptr)
    (selector arg1 arg2 arg3 : UInt256) (hb : ptr.toNat + 100 ≤ 2 ^ 200) :
    HeapMemory (callMem3 mem ptr selector arg1 arg2 arg3) (callWords3 aw ptr) ptr := by
  have hs := (callMem2_sizes h selector arg1 arg2).2.2
  have h68 : (ptr + ⟨68⟩).toNat = ptr.toNat + 68 :=
    addWord_toNat ptr ⟨68⟩ (by change ptr.toNat + 68 < 2 ^ 256; omega)
  have hh := (callMem2_heap h selector arg1 arg2 (by omega)).writeAbove (ptr + ⟨68⟩) arg3
    (by omega) (by omega) (by omega)
  simpa only [h68] using hh

theorem callMem3_prefix {mem aw ptr} (h : HeapMemory mem aw ptr)
    (selector arg1 arg2 arg3 : UInt256) :
    MemoryPrefix mem (callMem3 mem ptr selector arg1 arg2 arg3) ptr.toNat := by
  have hs := (callMem2_sizes h selector arg1 arg2).2.2
  exact (callMem2_prefix h selector arg1 arg2).trans
    (memoryPrefix_writeWord _ (ptr.toNat + 68) ptr.toNat arg3
      (by have hu := lt_usize 0 (by decide); omega) (Or.inl (by omega)))

theorem callMem3_read {mem aw ptr} (h : HeapMemory mem aw ptr)
    (selector arg1 arg2 arg3 : UInt256) :
    (callMem3 mem ptr selector arg1 arg2 arg3).readWithPadding ptr.toNat 100 =
      selector.toByteArray.extract 0 4 ++ arg1.toByteArray ++ arg2.toByteArray ++
        arg3.toByteArray := by
  have hs2 := (callMem2_sizes h selector arg1 arg2).2.2
  have hs3 := callMem3_size h selector arg1 arg2 arg3
  have hg : ptr.toNat + 68 - (callMem2 mem ptr selector arg1 arg2).size < USize.size := by
    have hu := lt_usize 0 (by decide)
    omega
  rw [show 100 = 68 + 32 from rfl, byteArray_readWithPadding_split _ ptr.toNat 68 32
    (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)]
  unfold callMem3
  rw [writeWord_read_preserved_len _ (ptr.toNat + 68) ptr.toNat 68 arg3 hg
    (Or.inl ⟨by omega, by omega⟩) (by decide) (by decide), callMem2_read h selector arg1 arg2,
    writeWord_read_back _ (ptr.toNat + 68) arg3 hg]

end Auction
