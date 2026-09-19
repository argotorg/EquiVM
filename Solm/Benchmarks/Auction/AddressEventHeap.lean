import Solm.Benchmarks.Auction.AddressEvent
import Solm.Benchmarks.Auction.MemoryGrowth
import Solm.Benchmarks.Auction.DepositPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

theorem addressEventHeap {mem aw ptr} (hm : HeapMemory mem aw ptr) (value : UInt256)
    (hb : ptr.toNat + 32 ≤ 2 ^ 200) :
    HeapMemory (addressEventMem mem aw value) (addressEventWords mem aw value) ptr := by
  have hp : addressEventPtr mem aw = ptr := hm.load64
  have hh : HeapMemory (addressEventMem mem aw value) (addressEventStoredWords mem aw) ptr := by
    simpa only [addressEventMem, addressEventStoredWords, hp, selectorMem,
      Reasoning.Theory.writeWord] using
      selectorMem_heap (hm.expand32 ⟨64⟩ (by decide)) (UInt256.land value solcAddrMask) hb
  have hl := hh.load64
  have hsub : UInt256.sub (UInt256.add ⟨32⟩ ptr) ptr = ⟨32⟩ := by
    rw [show UInt256.add ⟨32⟩ ptr = ptr + ⟨32⟩ from u256_add_comm _ _, word_add_sub_left]
  simp only [addressEventWords, hl, hp, hsub]
  exact (hh.expand32 ⟨64⟩ (by decide)).expand32 ptr hb

end Auction
