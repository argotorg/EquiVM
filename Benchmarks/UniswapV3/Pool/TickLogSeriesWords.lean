import Benchmarks.UniswapV3.Pool.TickLogSeriesSource
import Benchmarks.UniswapV3.Pool.TickLogRunWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

attribute [local irreducible] tickLogNext tickLogAccumulate

theorem tickLogStages_fold (r log : UInt256) :
    tickLogStages.foldl (fun state stage ↦ tickLogIteration state stage.2) (r, log) =
      (tickLogRun r 13, tickLogAccRun r log 13) := by
  rfl

theorem tickLogSeries_eq (price : UInt256) :
    tickLogSeries price =
      (tickLogRun (tickLogNormalized (tickLogRatio price) (tickLogMsb price).1) 13,
        tickLogAccRun (tickLogNormalized (tickLogRatio price) (tickLogMsb price).1)
          (tickLogInitial (tickLogMsb price).1) 13) :=
  tickLogStages_fold _ _

theorem tickLogResult_eq (price : UInt256) :
    tickLogResult price =
      tickLogAccRun (tickLogNormalized (tickLogRatio price) (tickLogMsb price).1)
        (tickLogInitial (tickLogMsb price).1) 14 := by
  rw [tickLogResult, tickLogSeries_eq]
  rfl

attribute [local semireducible] tickLogNext tickLogAccumulate

theorem tickLogAccRun_mask_step (r log : UInt256) (n : Nat) (hn : n ≤ 63) :
    UInt256.lor (UInt256.land (UInt256.ofNat (2 ^ (63 - n)))
      (UInt256.shiftRight (tickLogSquareAt r n) (UInt256.ofNat (192 + n))))
      (tickLogAccRun r log n) = tickLogAccRun r log (n + 1) := by
  have hcount : 192 + n = 255 - (63 - n) := by omega
  change UInt256.lor (UInt256.land (UInt256.ofNat (2 ^ (63 - n)))
    (UInt256.shiftRight (tickLogSquare (tickLogRun r n)) (UInt256.ofNat (192 + n))))
    (tickLogAccRun r log n) = _
  rw [hcount, tickLogContribution_eq _ _ (by omega)]
  exact u256_lor_comm _ _

end Benchmarks.UniswapV3.Pool
