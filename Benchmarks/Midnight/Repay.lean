import Benchmarks.Midnight.Dispatch

/-!
# Midnight `repay((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address,address,bytes)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 9725; reach lemma `midnightReachRepayBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

/-- `repay((uint256,address,address,(address,uint256,uint256,address)[],uint256,uint256,address,address),uint256,address,address,bytes)`: the theorem `Correct.lean` routes selector 19 to. -/
theorem midnightRepayBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 19)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 19) rfl hsel
  sorry

end Benchmarks.Midnight
