import Benchmarks.Dss.Jug.ConstructorSource
import Benchmarks.Dss.Jug.ConstructorTrace

/-!
# MakerDAO/Sky DSS Jug constructor correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem jugConstructorCorrect :
    constructorEquivalence config jugCreationBytecode contract jugBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases jugCtorDeployment_shape hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = jugCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := jugInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ_evm (jugCtorCallerWardsSlot I) ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σWards ⟨2⟩ (jugCtorVatStored σWards I vat)
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap = σVat := by
        simpa [σWards, σVat] using congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := jugCtorAfterWardsState evm0s
      let evm2s := jugCtorAfterVatState evm1s vat
      have hslot : wardsSlot (.address I.source) = jugCtorCallerWardsSlot I :=
        jugCtorCallerWardsSlot_eq I
      have hAccountsWards : accountMapEquiv σWards evm1s.accountMap := by
        simpa [σWards, evm1s, evm0s, jugCtorAfterWardsState, initState,
          storageStore_accountMap, storageStore_executionEnv, hslot] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (jugCtorCallerWardsSlot I) ⟨1⟩
            hAccounts
      have hOldVat :
          solcSlotWord σWards I ⟨2⟩ =
            Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨2⟩ := by
        simpa [evm1s, evm0s, jugCtorAfterWardsState, initState, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord, storageStore_executionEnv] using
          accountMapEquiv_storage_findD hAccountsWards I.codeOwner ⟨2⟩ ⟨0⟩
      have hAccountsVat : accountMapEquiv σVat evm2s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val))
          hAccountsWards
        simpa [σVat, σWards, evm2s, evm1s, jugCtorAfterVatState, storageStore_accountMap,
          storageStore_executionEnv, jugCtorVatStored, hOldVat] using hbase
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s] using
            jugSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [jugCtorAfterVatState, jugCtorAfterWardsState, storageStore_createdAccounts,
          initState]
      · simpa [evm2s] using hAccountsVat
  · have hrd := jugInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (jugSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Jug
