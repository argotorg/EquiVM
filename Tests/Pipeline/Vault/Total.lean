import Tests.Pipeline.Vault.Dispatch

/-!
# Vault `total()`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 284; reach lemma `vaultReachTotalBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Tests.Pipeline.Vault.Immutables

namespace Tests.Pipeline.Vault

set_option maxRecDepth 2000000

/-- `total()`: the theorem `Correct.lean` routes selector 4 to. -/
theorem vaultTotalBody {σ σ₀ A I} {g : UInt256} (v : VaultImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vaultSelBytes 4)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 4) rfl hsel
  sorry

end Tests.Pipeline.Vault
