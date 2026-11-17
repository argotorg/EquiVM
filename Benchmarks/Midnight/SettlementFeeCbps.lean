import Benchmarks.Midnight.Dispatch

/-!
# Midnight `settlementFeeCbps(bytes32)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 17792; reach lemma `midnightReachSettlementFeeCbpsBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `settlementFeeCbps(bytes32)`: the theorem `Correct.lean` routes selector 3 to. -/
theorem midnightSettlementFeeCbpsBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 3)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 3) rfl hsel
  sorry

end Benchmarks.Midnight
