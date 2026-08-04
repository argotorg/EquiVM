import Examples.Ripemd160Old.Oversized

/-!
# Original unoptimized RIPEMD-160 runtime equivalence

This theorem covers the deployed runtime from evmification commit `51429ca`. Constructor
equivalence is intentionally out of scope.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Ripemd160Old

open Ripemd160

theorem ripemd160OldCorrect :
    runtimeEquivalence config runtimeBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize _hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsmall : I.calldata.size ≤ maxFallbackCalldataSize
    · exact fallbackSuccess hcode hsize hwv hsmall hAccounts
    · exact fallbackOversized hcode hsize hwv (by omega)
  · exact fallbackNonPayable hcode hwv

def runtimeEquivalenceTarget : Prop :=
  runtimeEquivalence config runtimeBytecode contract

theorem runtimeEquivalenceTarget_proved : runtimeEquivalenceTarget :=
  ripemd160OldCorrect

end Ripemd160Old
