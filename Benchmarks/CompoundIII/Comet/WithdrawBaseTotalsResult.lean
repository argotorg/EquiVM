import Benchmarks.CompoundIII.Comet.WithdrawBaseTotalsModel

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

theorem withdrawBaseTotals_result {frame evm supplied borrowed result}
    (hb : ExecBlock fork config frame evm withdrawBaseTotalsBlock
      (withdrawBaseTotalsResult frame evm supplied borrowed))
    (he : withdrawBaseTotalsOutcome evm supplied borrowed = result) :
    ExecBlock fork config frame evm withdrawBaseTotalsBlock
      (match result with
       | .ok evm' => .ok frame evm'
       | .reverted => .reverted
       | .staticViolation => .staticViolation) := by
  cases result <;> simpa only [withdrawBaseTotalsResult, he] using hb

end Benchmarks.CompoundIII.Comet
