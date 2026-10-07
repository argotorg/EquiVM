import Benchmarks.Dss.Jug.ConstructorSource
import Benchmarks.Dss.Jug.ConstructorTrace
import Solm.Refine

/-!
# MakerDAO/Sky DSS Jug constructor correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem jugConstructorCorrect :
    typedConstructorRefinement config jugCreationBytecode contract (fun _ => jugBytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  rcases jugCtorDeployment_shape hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = jugCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := jugInitcodeSuccess (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact typedConstructorRefinementFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ (jugCtorCallerWardsSlot I) ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σWards ⟨2⟩ (jugCtorVatStored σWards I vat)
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hσ' : s.accountMap = σVat := by
        simpa [σWards, σVat] using hacc
      rw [hσ'] at hsuccess
      let evm0s := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := jugCtorAfterWardsState evm0s
      let evm2s := jugCtorAfterVatState evm1s vat
      have hslot : wardsSlot (.address I.source) = jugCtorCallerWardsSlot I :=
        jugCtorCallerWardsSlot_eq I
      have hMapWards : evm1s.accountMap = σWards := by
        simp [evm1s, evm0s, σWards, jugCtorAfterWardsState, initState,
          storageStore_accountMap, hslot]
      have hOldVat :
          solcSlotWord σWards I ⟨2⟩ =
            Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨2⟩ := by
        rw [← hMapWards]
        simp [evm1s, evm0s, jugCtorAfterWardsState, initState,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
          solcSlotWord, storageStore_executionEnv]
      have howner : evm1s.executionEnv.codeOwner = I.codeOwner := by
        simp [evm1s, evm0s, jugCtorAfterWardsState, storageStore_executionEnv, initState]
      have hMapVat : evm2s.accountMap = σVat := by
        unfold evm2s jugCtorAfterVatState
        rw [storageStore_accountMap, howner]
        dsimp [σVat, jugCtorVatStored]
        rw [hMapWards, ← howner, hOldVat.symm]
      refine typedConstructorRefinementFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s] using
            jugSolmCtorExecSuccess (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.success rfl rfl hMapVat.symm rfl
  · have hrd := jugInitcodeNonpayableRevert (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact typedConstructorRefinementFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine typedConstructorRefinementFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (jugSolmCtorExecReverts_nonpayable (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Jug
