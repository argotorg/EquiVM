import Benchmarks.Midnight.LiquidateFeesSource

/-! Liquidation arguments and accumulators survive the temporary locals of bad-debt recognition. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidateLossFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode total loss badDebt : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidateLossFrame frame total loss badDebt)
      m id index seized repaid borrower mode receiver callback data :=
  (((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateLossFrame_accumulators {frame : Frame}
    {bitmap maxDebt price originalDebt badDebt total loss : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt) :
    LiquidateAccumulators (liquidateLossFrame frame total loss badDebt)
      bitmap maxDebt price originalDebt badDebt :=
  (((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateLossFrame_loss (frame : Frame) (total loss badDebt : UInt256) :
    (liquidateLossFrame frame total loss badDebt).locals.get? "_lossFactor" =
      some (.int loss.toNat) := by
  simp only [liquidateLossFrame,
    wordLocal_get_ne _ _ _ _ (show "__c13" ≠ "_lossFactor" by decide),
    wordLocal_get_ne _ _ _ _ (show "__c12" ≠ "_lossFactor" by decide), wordLocal_get]

theorem liquidateFeeFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode oldLoss amount : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidateFeeFrame frame oldLoss amount)
      m id index seized repaid borrower mode receiver callback data := by
  dsimp only [liquidateFeeFrame]
  split
  · exact (((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)
  · exact h.insert _ _ (by decide)

theorem liquidateFeeFrame_accumulators {frame : Frame}
    {bitmap maxDebt price originalDebt badDebt oldLoss amount : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt) :
    LiquidateAccumulators (liquidateFeeFrame frame oldLoss amount)
      bitmap maxDebt price originalDebt badDebt := by
  dsimp only [liquidateFeeFrame]
  split
  · exact (((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)
  · exact h.insert _ _ (by decide)

end Benchmarks.Midnight
