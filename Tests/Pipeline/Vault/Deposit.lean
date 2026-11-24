import Tests.Pipeline.Vault.Dispatch

variable {fork : Ethereum.Fork}

/-!
# Vault `deposit(uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 383; reach lemma `vaultReachDepositBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Tests.Pipeline.Vault.Immutables

namespace Tests.Pipeline.Vault

set_option maxRecDepth 2000000

/-- `deposit(uint256)`: the theorem `Correct.lean` routes selector 8 to. -/
theorem vaultDepositBody {σ σ₀ A I} {g : UInt256} (v : VaultImmutables)
    (hcode : I.code = deployedRuntime v) (hsize : I.calldata.size < UInt256.size)
    (hwv : I.weiValue = ⟨0⟩)
    (hsel : selIs I (vaultSelBytes 8)) :
    runtimeRefinementFor fork config contract σ σ₀ g A I (immStore v) := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (vaultSelBytes 8) rfl hsel
  sorry

end Tests.Pipeline.Vault
