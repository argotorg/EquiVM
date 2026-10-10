import Benchmarks.CompoundIII.Comet.SupplyBaseTotalsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem supplyBaseTotals_result {frame evm supplied repaid result}
    (hb : ExecBlock config frame evm supplyBaseTotalsBlock
      (supplyBaseTotalsResult frame evm supplied repaid))
    (he : supplyBaseTotalsOutcome evm supplied repaid = result) :
    ExecBlock config frame evm supplyBaseTotalsBlock
      (match result with
       | .ok evm' => .ok frame evm'
       | .reverted => .reverted
       | .staticViolation => .staticViolation) := by
  cases result <;> simpa only [supplyBaseTotalsResult, he] using hb

end Benchmarks.CompoundIII.Comet
