import Benchmarks.EAS.Attester.ConstructorTrace
import Solm.Refine

/-!
# EAS Attester constructor correctness stub

The constructor sets `_eas`.  `typedConstructorRefinement` checks that the runtime the EVM returns
is the template patched with the constructor's final immutables (`deployedRuntime`), and that those
are well typed.  Proof left as the benchmark target.
-/

open Solm ABI Ethereum Ethereum.EVM Benchmarks.EAS.Attester.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem attesterConstructorCorrect :
    typedConstructorRefinement config attesterCreationBytecode contract
      (deployedRuntime attesterBytecode) := by
  intro σ σ₀ g A I args code hdeploy hcode _hcalldata _hperm
  obtain ⟨eas, rfl, hdeployed⟩ := constructorDeployment_shape hdeploy
  rw [hdeployed] at hcode
  have hcode' : I.code = constructorCode eas := hcode
  by_cases hv : I.weiValue = ⟨0⟩
  · by_cases hz : eas = ⟨0, by decide⟩
    · have hr := constructorZeroTrace (σ := σ) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
        (A := A) eas hcode' hv hz
      rcases hr.xiResult hcode' with hoog | ⟨gasLeft, out, hrev⟩
      · exact .outOfGas (by simpa only [Sat256.ofUInt256] using hoog)
      · exact .execution hrev (constructorSourceZero eas hv hz) (.revert rfl rfl) trivial
    · have hr := constructorSuccessTrace (σ := σ) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
        (A := A) eas hcode' hv hz
      rcases hr.xiResult hcode' with hoog | ⟨gasLeft, A', hsuccess⟩
      · exact .outOfGas (by simpa only [Sat256.ofUInt256] using hoog)
      · exact .execution hsuccess (constructorSourceSuccess eas hv hz)
          (.success rfl rfl rfl rfl) (constructorFinalImms_fit eas)
  · have hr := constructorNonpayableTrace (σ := σ) (σ₀ := σ₀) (g := Sat256.ofUInt256 g)
      (A := A) hcode hv
    rcases hr.xiResult hcode with hoog | ⟨gasLeft, out, hrev⟩
    · exact .outOfGas (by simpa only [Sat256.ofUInt256] using hoog)
    · exact .execution hrev (constructorSourceNonpayable eas hv) (.revert rfl rfl) trivial

end Benchmarks.EAS.Attester
