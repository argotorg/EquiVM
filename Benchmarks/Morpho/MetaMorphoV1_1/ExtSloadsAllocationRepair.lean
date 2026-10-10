import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsSimulation
import Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsOversizedCallee

/-! The explicit source allocation rejects the previously exhibited real oversized return. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationRegression

open SourceMemory

set_option autoImplicit false

theorem oversizedReturn_allocationDoesNotFit :
    ¬ allocationFits ⟨512⟩ (UInt256.ofNat oversizedReturn.size) := by
  intro hfit
  have hguard := (allocationGuard_eq_zero_iff ⟨512⟩ (UInt256.ofNat oversizedReturn.size)).mpr hfit
  have hreject : allocationGuardWord ⟨512⟩ (UInt256.ofNat oversizedReturn.size) = ⟨1⟩ :=
    oversizedReturn_allocatorRejects
  exact (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hreject.symm.trans hguard)

/-- This uses the actual successful call witness; no alternate failing call is substituted. -/
theorem oversizedReturn_repairedSourceReverts (slot : UInt256) (imms : Store) :
    ExecFuncBody config
      (extSloadsFrame { contract := contract, locals := ∅, immutables := imms }
        ⟨512⟩ oversizedCalleeAddress [wordBytes32Value slot]) oversizedCallerState
      extSloadsFunction.body .reverted := by
  exact extSloadsBodyBufferReverts ⟨512⟩ oversizedCalleeAddress _ oversizedReturn
    allocateFunction_lookup (oversizedCalleeTypedCall slot)
    (by rw [oversizedReturn_size]; decide +kernel) oversizedReturn_allocationDoesNotFit

end Benchmarks.Morpho.MetaMorphoV1_1.ExtSloadsAllocationRegression
