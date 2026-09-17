import Benchmarks.Auction.SparseMemory
import Benchmarks.Auction.MemoryGrowth

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: two ABI words written at the free cursor for an event payload.
noncomputable def pairEventMem (mem : ByteArray) (ptr first second : UInt256) : ByteArray :=
  writeWord (writeWord mem ptr.toNat first) (ptr.toNat + 32) second

def pairEventWords (aw ptr : UInt256) : UInt256 :=
  expandedWords (expandedWords (expandedWords aw ptr ⟨32⟩) (ptr + ⟨32⟩) ⟨32⟩) ptr ⟨64⟩

theorem pairEventHeap {mem aw ptr first second} (hm : MemoryCursor mem aw ptr)
    (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    HeapMemory (pairEventMem mem ptr first second) (pairEventWords aw ptr) ptr := by
  have hp : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  have h1 := hm.writeAbove ptr first (le_refl _) (by omega)
  have h2 := h1.cursor.writeAbove (ptr + ⟨32⟩) second (by omega) (by omega)
  rw [hp] at h2
  exact ⟨h2.size, h2.free, h2.lower, h2.gap, activeWords_expand h2.active hb⟩

theorem pairEventPrefix (mem : ByteArray) (ptr first second : UInt256) :
    MemoryPrefix mem (pairEventMem mem ptr first second) ptr.toNat :=
  (memoryPrefix_sparse_writeWord mem ptr.toNat ptr.toNat first (Or.inl (le_refl _))).trans
    (memoryPrefix_sparse_writeWord _ (ptr.toNat + 32) ptr.toNat second (Or.inl (by omega)))

theorem pairEventGrowth {aw ptr} (ha : ActiveWords aw) (hb : ptr.toNat + 64 ≤ 2 ^ 200) :
    aw.toNat ≤ (pairEventWords aw ptr).toNat := by
  have hp : (ptr + ⟨32⟩).toNat = ptr.toNat + 32 :=
    addWord_toNat ptr ⟨32⟩ (by change ptr.toNat + 32 < 2 ^ 256; omega)
  have hb32 : ptr.toNat + 32 ≤ 2 ^ 200 := by omega
  have hb2 : (ptr + ⟨32⟩).toNat + 32 ≤ 2 ^ 200 := by omega
  have ha1 := activeWords_expand32 ha hb32
  have ha2 := activeWords_expand32 ha1 hb2
  exact le_trans (le_trans (expandedWords_mono ha hb32) (expandedWords_mono ha1 hb2))
    (expandedWords_mono ha2 hb)

end Auction
