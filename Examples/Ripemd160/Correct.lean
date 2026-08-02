import Examples.Ripemd160.SolmFallback

/-!
# Ripemd160Deployed runtime equivalence

The contract has no selector-based entries: runtime calls enter the raw fallback. Constructor
equivalence is intentionally out of scope.
-/

open Solm ABI Ethereum Ethereum.EVM

namespace Ripemd160

theorem ripemd160Correct :
    runtimeEquivalence config ripemd160RuntimeBytecode contract := by
  refine ⟨fun cA gh bl σ_evm σ_solm σ₀ g A I hcode hsize _hperm hAccounts => ?_⟩
  by_cases hwv : I.weiValue = ⟨0⟩
  · by_cases hsmall : I.calldata.size ≤ maxFallbackCalldataSize
    · exact fallbackSuccess hcode hsize hwv hsmall hAccounts
    · exact fallbackOversized hcode hsize hwv (by omega)
  · exact fallbackNonPayable hcode hwv

def runtimeEquivalenceTarget : Prop :=
  runtimeEquivalence config ripemd160RuntimeBytecode contract

theorem runtimeEquivalenceTarget_proved : runtimeEquivalenceTarget :=
  ripemd160Correct

end Ripemd160
