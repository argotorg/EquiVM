import Benchmarks.Midnight.LiquidateDecode
import Benchmarks.Midnight.CalldataArgumentSlice

/-! Failure and success facts used while checking liquidation's arguments. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000

theorem decodeLiquidateArguments_none_market {bytes : ByteArray}
    (h : decodeCalldataMarket bytes 4 = none) : decodeLiquidateArguments bytes = none := by
  unfold decodeLiquidateArguments
  rw [h]
  rfl

theorem decodeLiquidateArguments_none_scalars {bytes : ByteArray}
    (h : ¬ LiquidateScalarsValid bytes) : decodeLiquidateArguments bytes = none := by
  unfold decodeLiquidateArguments
  cases decodeCalldataMarket bytes 4 with
  | none => rfl
  | some m =>
    dsimp only [bind, Option.bind]
    rw [if_neg (fun hc ↦ h hc.1)]

theorem decodeLiquidateArguments_none_data {bytes : ByteArray}
    (h : ¬ CalldataArgumentValid true bytes 260) : decodeLiquidateArguments bytes = none := by
  unfold decodeLiquidateArguments
  cases decodeCalldataMarket bytes 4 with
  | none => rfl
  | some m =>
    dsimp only [bind, Option.bind]
    split
    · rw [decodeCalldataBytes_invalid h]
    · rfl

end Benchmarks.Midnight
