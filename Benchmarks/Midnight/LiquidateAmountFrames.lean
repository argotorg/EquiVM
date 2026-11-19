import Benchmarks.Midnight.LiquidateConversionSource

/-! Update liquidation's amount locals while preserving its other arguments and accumulators. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem LiquidateSourceFrame.setRepaid {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode value : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (wordLocal frame "repaidUnits" value)
      m id index seized value borrower mode receiver callback data := by
  rcases h with ⟨hc, hm, hi, hidx, hs, hr, hbor, hmode, hrecv, hcb, hd, hp, hms⟩
  constructor <;> simp_all [wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem LiquidateSourceFrame.setSeized {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode value : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (wordLocal frame "seizedAssets" value)
      m id index value repaid borrower mode receiver callback data := by
  rcases h with ⟨hc, hm, hi, hidx, hs, hr, hbor, hmode, hrecv, hcb, hd, hp, hms⟩
  constructor <;> simp_all [wordLocal, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]

theorem liquidateSeizeFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode price lif : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidateSeizeFrame frame seized price lif)
      m id index seized (liquidateRepaidAmount seized price lif) borrower mode receiver callback data :=
  ((h.insert _ _ (by decide)).insert _ _ (by decide)).setRepaid

theorem liquidateRepayFrame_arguments {frame : Frame} {m : MarketData}
    {id index seized repaid borrower mode price lif : UInt256}
    {receiver callback : AccountAddress} {data : ByteArray}
    (h : LiquidateSourceFrame frame m id index seized repaid borrower mode receiver callback data) :
    LiquidateSourceFrame (liquidateRepayFrame frame repaid price lif)
      m id index (liquidateSeizedAmount repaid price lif) repaid borrower mode receiver callback data :=
  ((h.insert _ _ (by decide)).insert _ _ (by decide)).setSeized

theorem liquidateSeizeFrame_accumulators {frame : Frame}
    {bitmap maxDebt price originalDebt badDebt seized lif : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt) :
    LiquidateAccumulators (liquidateSeizeFrame frame seized price lif)
      bitmap maxDebt price originalDebt badDebt :=
  ((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateRepayFrame_accumulators {frame : Frame}
    {bitmap maxDebt price originalDebt badDebt repaid lif : UInt256}
    (h : LiquidateAccumulators frame bitmap maxDebt price originalDebt badDebt) :
    LiquidateAccumulators (liquidateRepayFrame frame repaid price lif)
      bitmap maxDebt price originalDebt badDebt :=
  ((h.insert _ _ (by decide)).insert _ _ (by decide)).insert _ _ (by decide)

theorem liquidateSeizeFrame_get (frame : Frame) (seized price lif : UInt256) (name : Ident)
    (hn : name ∉ ["__c19", "__c20", "repaidUnits"]) :
    (liquidateSeizeFrame frame seized price lif).locals.get? name = frame.locals.get? name := by
  simp only [List.mem_cons, List.mem_singleton, not_or] at hn
  simp only [liquidateSeizeFrame, wordLocal_get_ne _ _ _ _ (Ne.symm hn.1),
    wordLocal_get_ne _ _ _ _ (Ne.symm hn.2.1), wordLocal_get_ne _ _ _ _ (Ne.symm hn.2.2.1)]

theorem liquidateRepayFrame_get (frame : Frame) (repaid price lif : UInt256) (name : Ident)
    (hn : name ∉ ["__c21", "__c22", "seizedAssets"]) :
    (liquidateRepayFrame frame repaid price lif).locals.get? name = frame.locals.get? name := by
  simp only [List.mem_cons, List.mem_singleton, not_or] at hn
  simp only [liquidateRepayFrame, wordLocal_get_ne _ _ _ _ (Ne.symm hn.1),
    wordLocal_get_ne _ _ _ _ (Ne.symm hn.2.1), wordLocal_get_ne _ _ _ _ (Ne.symm hn.2.2.1)]

end Benchmarks.Midnight
