import Benchmarks.Midnight.LiquidatePositionMemory

/-! The saved ID and market slot after liquidation's position lookup. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidatePositionMemory_id {mem : ByteArray} (id borrower : UInt256)
    (hm : 832 ≤ mem.size) :
    memLoad (UInt256.ofNat 768) (liquidatePositionMemory mem id borrower) = id := by
  have hp := positionReadMemory_prefix (liquidateMarketMemory mem id) id borrower 832
  rw [liquidatePositionMemory, hp.load _ (by decide) (by decide)
    (by rw [liquidateMarketMemory_size id hm]; change 800 ≤ mem.size; omega),
    liquidateMarketMemory_id id hm]

theorem liquidatePositionMemory_slot {mem : ByteArray} (id borrower : UInt256)
    (hm : 832 ≤ mem.size) :
    memLoad (UInt256.ofNat 672) (liquidatePositionMemory mem id borrower) =
      solcMappingSlot ⟨1⟩ id := by
  have hp := positionReadMemory_prefix (liquidateMarketMemory mem id) id borrower 832
  rw [liquidatePositionMemory, hp.load _ (by decide) (by decide)
    (by rw [liquidateMarketMemory_size id hm]; change 704 ≤ mem.size; omega)]
  exact memLoad_writeWord _ (UInt256.ofNat 672) _

end Benchmarks.Midnight
