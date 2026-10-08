import Tests.Pipeline.Vault.Common

/-!
# Vault constructor correctness

Creation-code equivalence: the constructor's EVM trace (argument decode, stores, runtime-code
return) against the Solm constructor body, composed from the creation summaries.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Tests.Pipeline.Vault.Immutables

namespace Tests.Pipeline.Vault

theorem vaultConstructorCorrect :
    typedConstructorRefinement config vaultCreationBytecode contract (immutableLayout.deployed vaultBytecode) := by
  sorry

end Tests.Pipeline.Vault
