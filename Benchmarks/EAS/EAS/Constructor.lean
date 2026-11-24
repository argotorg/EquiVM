import Benchmarks.EAS.EAS.ConstructorReturnTrace

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Immutables
namespace Benchmarks.EAS.EAS

theorem easConstructorCorrect :
    typedConstructorRefinement config easCreationBytecode contract (immutableLayout.deployed easBytecode) := by
  intro fork _hfork σ σ₀ g A I args code hdeploy hcode _hcalldata _hperm
  obtain ⟨registry,rfl,hdeployed⟩ := easCtorDeployment_shape hdeploy
  rw [hdeployed] at hcode
  have hcode' : I.code = easCtorCode registry := hcode
  by_cases hv : I.weiValue = ⟨0⟩
  · have hsource := easCtorSource (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := g) registry hv
    by_cases hz : registry = ⟨0,by decide⟩
    · rw [if_pos hz] at hsource
      have hr := easCtorZeroTrace (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) registry hcode' hv hz
      rcases hr.xiResult hcode' with hoog | ⟨gasLeft,out,hrev⟩
      · exact .outOfGas (by simpa only [Sat256.ofUInt256] using hoog)
      · exact .execution hrev hsource (.revert rfl rfl) trivial
    · rw [if_neg hz] at hsource
      have hr := easCtorSuccessTrace (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) registry hcode' hv hz
      rcases hr.xiResult hcode' with hoog | ⟨gasLeft,A',hret⟩
      · exact .outOfGas (by simpa only [Sat256.ofUInt256] using hoog)
      · exact .execution hret hsource (.success rfl rfl rfl rfl) (easCtorImms_fit I.codeOwner registry)
  · have hr := easCtorNonpayableTrace (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hv
    rcases hr.xiResult hcode with hoog | ⟨gasLeft,out,hrev⟩
    · exact .outOfGas (by simpa only [Sat256.ofUInt256] using hoog)
    · exact .execution hrev (easCtorSourceNonpayable registry hv) (.revert rfl rfl) trivial

end Benchmarks.EAS.EAS
