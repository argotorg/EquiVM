import Benchmarks.Midnight.LiquidateLif

/-! The argument and accumulator invariants through liquidation's incentive calculation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem liquidateMaxLifFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode lltv cursor : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidateMaxLifFrame frame lltv cursor)
      m id index seized repaid borrower mode receiver callback data :=
  ((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateMaxLifFrame_accumulators {frame : Frame}
    {bitmap maxDebt price originalDebt badDebt lltv cursor : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt) :
    LiquidateAccumulators (liquidateMaxLifFrame frame lltv cursor)
      bitmap maxDebt price originalDebt badDebt :=
  ((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateLifFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode maximum timestamp maturity : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidateLifFrame frame mode maximum timestamp maturity)
      m id index seized repaid borrower mode receiver callback data := by
  unfold liquidateLifFrame
  split
  · exact h
  · exact (h.insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateLifFrame_accumulators {frame : Frame}
    {bitmap maxDebt price originalDebt badDebt mode maximum timestamp maturity : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt) :
    LiquidateAccumulators (liquidateLifFrame frame mode maximum timestamp maturity)
      bitmap maxDebt price originalDebt badDebt := by
  unfold liquidateLifFrame
  split
  · exact h
  · exact (h.insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateLifFrame_get {frame : Frame} {mode maximum timestamp maturity : UInt256}
    (h : frame.locals.get? "lif" = some (.int maximum.toNat)) :
    (liquidateLifFrame frame mode maximum timestamp maturity).locals.get? "lif" =
      some (.int (liquidateLif mode maximum timestamp maturity).toNat) := by
  unfold liquidateLifFrame liquidateLif
  split
  · exact h
  · exact wordLocal_get _ _ _

theorem liquidateLifFrame_lltv {frame : Frame} {mode maximum timestamp maturity lltv : UInt256}
    (h : frame.locals.get? "lltv" = some (.int lltv.toNat)) :
    (liquidateLifFrame frame mode maximum timestamp maturity).locals.get? "lltv" =
      some (.int lltv.toNat) := by
  unfold liquidateLifFrame
  split
  · exact h
  · simpa only [liquidateGrownFrame,
      wordLocal_get_ne _ _ _ _ (show "lif" ≠ "lltv" by decide),
      wordLocal_get_ne _ _ _ _ (show "grown" ≠ "lltv" by decide)] using h

end Benchmarks.Midnight
