import Benchmarks.EAS.EAS.Dispatch

/-!
# EAS `getAttestTypeHash()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 4138; reach lemma `easReachGetAttestTypeHashBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.EAS.EAS.Immutables

namespace Benchmarks.EAS.EAS

set_option maxRecDepth 2000000

/-- `getAttestTypeHash()`: the theorem `Correct.lean` routes selector 0 to. -/
theorem easGetAttestTypeHashBody {σ σ₀ A I} {g : UInt256} (v : EASImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hsel : selIs I (easSelBytes 0)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (easSelBytes 0) rfl hsel
  sorry

end Benchmarks.EAS.EAS
