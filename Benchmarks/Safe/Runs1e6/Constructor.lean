import Benchmarks.Safe.Runs1e6.Bytecode
import Benchmarks.Safe.Runs1e6.ConstructorTrace
import Stele.Refine

variable {fork : Ethereum.Fork}

/-!
# Safe constructor correctness stub

The optimized creation bytecode, deployed runtime bytecode, and Stele constructor specification are
present. The constructor-equivalence proof is intentionally left as the benchmark target.
-/

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.Runs1e6

theorem safeConstructorBodyCore :
    typedConstructorRefinement config safeCreationBytecode contract (fun _ ↦ safeBytecode) := by
  intro fork _hfork σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  have hlen := emptyCtorDeployment_args_length (cfg := config) (contract := contract)
    rfl rfl hdeploy
  have hdeployed := emptyCtorDeployment_eq_initcode (cfg := config) (contract := contract)
    rfl rfl hdeploy
  have hargs : args = [] := List.eq_nil_of_length_eq_zero hlen
  subst args
  rw [hdeployed] at hcode
  by_cases hv : I.weiValue = ⟨0⟩
  · have hr := safeConstructorTrace (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode hv hperm
    exact hr.constructorRefinementEmptyParams hcode rfl
      (safeConstructorSource (fork := fork) (hperm := by assumption) _ hv) (by rw [storageStore_accountMap]; rfl)
  · have hr := safeConstructorTraceRevert (fork := fork) (σ := σ) (σ₀ := σ₀) (A := A)
      (g := Sat256.ofUInt256 g) hcode hv
    exact hr.constructorRefinementEmptyParams hcode rfl (safeConstructorSourceRevert _ hv)

theorem safeConstructorCorrect :
    typedConstructorRefinement config safeCreationBytecode contract (fun _ ↦ safeBytecode) :=
  safeConstructorBodyCore

end Benchmarks.Safe.Runs1e6
