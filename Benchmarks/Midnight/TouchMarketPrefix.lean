import Benchmarks.Midnight.MarketIdWorkMemory
import Benchmarks.Midnight.TouchMarketSourceBase
import Benchmarks.Midnight.RuntimeBlocks_079
import Benchmarks.Midnight.MappingMemory

variable {fork : Ethereum.Fork}

/-! Market-ID calculation followed by the existing-market check in touchMarket. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def touchMarketHashMemory (mem : ByteArray) (root : UInt256) (m : MarketData) : ByteArray :=
  twoWordHashMem m.id (UInt256.ofNat 1) (marketIdWorkMemory mem root m)

theorem touchMarketHashMemory_prefix (mem : ByteArray) {root : UInt256} (m : MarketData)
    (hlo : 96 ≤ root.toNat) (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64) :
    MemoryPrefix mem (touchMarketHashMemory mem root m) root.toNat := by
  exact ((marketIdWorkMemory_prefix mem m hlo hb).trans
    (memoryPrefix_writeWord _ 0 _ _ (Or.inr (by decide)))).trans
    (memoryPrefix_writeWord _ 32 _ _ (Or.inr (by decide)))

set_option maxRecDepth 2000000 in
theorem midnightTouchMarketPrefix {evm : EVM.State} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root ptr arrayPtr ret : UInt256} {k C : Nat} {R : List UInt256}
    (m : MarketData) (hstack : R.length + 26 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr root m)
    (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (rd : RD fork midnightBytecode evm.executionEnv g s0 ⟨20557⟩ (ptr :: ret :: R)
      mem aw rdata evm.accountMap k C) :
    (marketTickSpacing (marketFeeWord evm m.id) ≠ ⟨0⟩ ∧
      ∃ aw' k' C', RD fork midnightBytecode evm.executionEnv g s0 ret (m.id :: R)
        (touchMarketHashMemory mem root m) aw' rdata evm.accountMap k' C') ∨
    (marketTickSpacing (marketFeeWord evm m.id) = ⟨0⟩ ∧
      ∃ aw' k' C', RD fork midnightBytecode evm.executionEnv g s0 ⟨20764⟩
        ((ptr + UInt256.ofNat 32) :: ptr :: m.id :: ret :: R)
        (touchMarketHashMemory mem root m) aw' rdata evm.accountMap k' C') := by
  have hlo : 96 ≤ root.toNat := by
    have := hm.lower; have := hm.array; have := hm.extent; omega
  obtain ⟨aw1, k1, C1, rd1⟩ := midnightMarketIdTrace m
    (by simp only [List.length_cons]; omega) hm hb hfree rd
  have hlen := marketIdWorkMemory_length mem m hlo hb
  have hhash := marketIdWorkMemory_hash mem m hlo hb
  have hmem : 64 ≤ (marketIdWorkMemory mem root m).size := by
    dsimp only [marketIdWorkMemory, marketIdMemory]
    rw [writeWord_sparse_size]; omega
  have hh : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem m.id (UInt256.ofNat 1) (marketIdWorkMemory mem root m)) =
      solcMappingSlot ⟨1⟩ m.id := twoWordHashMem_mapSlot_of_ge64 m.id (UInt256.ofNat 1) hmem
  by_cases hinit : marketTickSpacing (marketFeeWord evm m.id) = ⟨0⟩
  · obtain ⟨aw2, k2, C2, rd2⟩ := midnightBlocks.midnight_block_20728_taken_packed
      (by simp only [List.length_cons]; omega) (by
        simp only [hlen, hhash, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh]
        change UInt256.isZero (marketTickSpacing (marketFeeWord evm m.id)) ≠ UInt256.ofNat 0
        rw [hinit]; decide) (by jump_dest) rd1
    simp only [midnightBlocks.midnight_block_20728_taken_stack,
      midnightBlocks.midnight_block_20728_taken_memory, hlen, hhash] at rd2
    exact Or.inr ⟨hinit, _, _, _, rd2⟩
  · obtain ⟨aw2, k2, C2, rd2⟩ := midnightBlocks.midnight_block_20728_fallthrough_packed
      (by simp only [List.length_cons]; omega) (by
        simp only [hlen, hhash, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
          show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold, hh]
        exact isZero_eq_zero_of_ne hinit) rd1
    simp only [midnightBlocks.midnight_block_20728_fallthrough_stack,
      midnightBlocks.midnight_block_20728_fallthrough_memory, hlen, hhash] at rd2
    have rd3 := midnightBlocks.midnight_block_20760 (by omega) hret rd2
    exact Or.inl ⟨hinit, _, _, _, rd3⟩

end Benchmarks.Midnight
