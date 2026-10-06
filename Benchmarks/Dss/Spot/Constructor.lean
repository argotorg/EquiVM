import Benchmarks.Dss.Spot.ConstructorSource
import Benchmarks.Dss.Spot.ConstructorTrace

/-!
# MakerDAO/Sky DSS Spotter constructor correctness

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
connected by the constructor-equivalence proof.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem spotConstructorCorrect :
    constructorEquivalence config spotCreationBytecode contract spotBytecode := by
  refine constructorEquivalence.intro ?_
  intro σ σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm
  rcases spotCtorDeployment_shape hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = spotCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := spotInitcodeSuccess
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ (spotCtorCallerWardsSlot I) ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σWards ⟨2⟩ (spotCtorVatStored σWards I vat)
      let σPar := sstoreAccountMap I.codeOwner σVat ⟨3⟩ spotCtorOneWord
      let σLive := sstoreAccountMap I.codeOwner σPar ⟨4⟩ ⟨1⟩
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hσ' : s.accountMap = σLive := by
        simpa [σWards, σVat, σPar, σLive] using hacc
      rw [hσ'] at hsuccess
      let evm0s :=
        initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := spotCtorAfterWardsState evm0s
      let evm2s := spotCtorAfterVatState evm1s vat
      let evm3s := spotCtorAfterParState evm2s
      let evm4s := spotCtorAfterLiveState evm3s
      have hslot : wardsSlot (.address I.source) = spotCtorCallerWardsSlot I :=
        spotCtorCallerWardsSlot_eq I
      have hAccountsWards : σWards = evm1s.accountMap := by
        simp [σWards, evm1s, evm0s, spotCtorAfterWardsState, initState,
          storageStore_accountMap, storageStore_executionEnv, hslot]
      have hOldVat :
          solcSlotWord σWards I ⟨2⟩ =
            Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨2⟩ := by
        unfold solcSlotWord Solm.EVM.storageLoad
        rw [hAccountsWards]
        simp [evm1s, evm0s, spotCtorAfterWardsState, initState,
          State.lookupAccount, Account.lookupStorage, storageStore_executionEnv]
      have hAccountsVat : σVat = evm2s.accountMap := by
        have hvalue :
            spotCtorVatStored σWards I vat =
              setAddressOffset0Word
                (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨2⟩)
                (EVM.word vat.val) := by
          unfold spotCtorVatStored
          rw [hOldVat]
        simp only [σVat, evm2s, spotCtorAfterVatState, storageStore_accountMap]
        rw [hvalue, ← hAccountsWards]
        simp [evm1s, evm0s, spotCtorAfterWardsState, initState,
          storageStore_executionEnv]
      have hAccountsPar : σPar = evm3s.accountMap := by
        simp [σPar, evm3s, evm2s, evm1s, evm0s, spotCtorAfterParState,
          spotCtorAfterVatState, spotCtorAfterWardsState, initState, storageStore_accountMap,
          storageStore_executionEnv, hAccountsVat]
      have hAccountsLive : σLive = evm4s.accountMap := by
        simp [σLive, evm4s, evm3s, evm2s, evm1s, evm0s, spotCtorAfterLiveState,
          spotCtorAfterParState, spotCtorAfterVatState, spotCtorAfterWardsState, initState,
          storageStore_accountMap, storageStore_executionEnv, hAccountsPar]
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s] using
            spotSolmCtorExecSuccess
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ rfl
      exact hAccountsLive
  · have hrd := spotInitcodeNonpayableRevert
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (spotSolmCtorExecReverts_nonpayable
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Spot
