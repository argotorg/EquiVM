import Benchmarks.OpenZeppelinBench.TimelockController.ConstructorEvm
import Benchmarks.OpenZeppelinBench.TimelockController.ConstructorSolm

/-!
# OpenZeppelin TimelockController constructor correctness

The optimized creation bytecode deploys the concrete payable wrapper with initial delay `1 days`,
`msg.sender` as admin/proposer/canceller, and `address(0)` as open executor.  The proof assembles the
EVM creation trace (`tlcCtorInitcodeSuccess`) and the Solm constructor execution
(`tlcCtorSolmExecSuccess`) through the constructor-equivalence bridge, reconciling the two final
account maps with `tlcCtorFinalMap_reconcile`.  The constructor is payable, so there is no
callvalue-revert path.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace OpenZeppelinBench.TimelockController

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem timelockControllerBenchConstructorCorrect :
    constructorEquivalence config timelockControllerBenchCreationBytecode contract
      timelockControllerBenchBytecode := by
  refine constructorEquivalence.intro ?_
  intro cA gh bl σ_evm σ_solm σ₀ g A I args deployedInitcode hdeploy hcode hcalldata hperm hσ
  have hdeployed := emptyCtorDeployment_eq_initcode tlc_selfDeployment_eq tlc_ctor_params_nil hdeploy
  rw [hdeployed] at hcode
  obtain rfl : args = [] := by
    have := emptyCtorDeployment_args_length tlc_selfDeployment_eq tlc_ctor_params_nil hdeploy
    rw [tlc_ctor_params_nil] at this
    exact List.eq_nil_of_length_eq_zero this
  have hrd := tlcCtorInitcodeSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm)
    (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g) hcode hperm hcalldata
  rcases hrd with hoog | ⟨s, hX, hacc⟩
  · exact constructorEquivalenceFor.outOfGas (Xi_error_of_X (g := g) (by
      rw [← hcode] at hoog; simpa [Sat256.ofUInt256] using hoog))
  · have hsuccess := Xi_success_of_X (g := g) (by
      rw [← hcode] at hX; simpa [Sat256.ofUInt256] using hX)
    have hcA : s.createdAccounts = cA := congrArg Prod.fst hacc
    have hσ' : s.accountMap = tlcCtorFinalMap I σ_evm := congrArg Prod.snd hacc
    rw [hcA, hσ'] at hsuccess
    obtain ⟨frame, S, hexec, hScA, hSmap⟩ :=
      tlcCtorSolmExecSuccess (cA := cA) (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀)
        (A := A) (I := I) (g := g)
    refine constructorEquivalenceFor.execution hsuccess hexec ?_
    refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
    · exact hScA.symm
    · rw [hSmap]
      exact tlcCtorFinalMap_reconcile I hσ

end OpenZeppelinBench.TimelockController
