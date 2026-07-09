import Benchmarks.Dss.Cat.ConstructorSource
import Benchmarks.Dss.Cat.ConstructorTraceReturn

/-!
# MakerDAO/Sky DSS Cat constructor correctness

The Cat constructor stores three slots — `wards[sender] = 1`, `vat = vat_` (address slot 3),
`live = 1` (scalar slot 2) — matching the optimized creation bytecode's store order.  The EVM trace
lives in `ConstructorTrace*`, the Solm source semantics in `ConstructorSource`, and this file
assembles the two through the account-map-equivalence chain.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem catConstructorCorrect :
    constructorEquivalence config catCreationBytecode contract catBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases catCtorDeployment_shape hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = catCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := catInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ_evm (catCtorCallerWardsSlot I) ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σWards ⟨3⟩ (catCtorVatStored σWards I vat)
      let σLive := sstoreAccountMap I.codeOwner σVat ⟨2⟩ ⟨1⟩
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap = σLive := by
        simpa [σWards, σVat, σLive] using congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := catCtorAfterWardsState evm0s
      let evm2s := catCtorAfterVatState evm1s vat
      let evm3s := catCtorAfterLiveState evm2s
      have hslot : wardsSlot (.address I.source) = catCtorCallerWardsSlot I :=
        catCtorCallerWardsSlot_eq I
      have hAccountsWards : accountMapEquiv σWards evm1s.accountMap := by
        simpa [σWards, evm1s, evm0s, catCtorAfterWardsState, initState,
          storageStore_accountMap, storageStore_executionEnv, hslot] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (catCtorCallerWardsSlot I) ⟨1⟩
            hAccounts
      have hOldVat :
          solcSlotWord σWards I ⟨3⟩ =
            Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨3⟩ := by
        simpa [evm1s, evm0s, catCtorAfterWardsState, initState, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord, storageStore_executionEnv] using
          accountMapEquiv_storage_findD hAccountsWards I.codeOwner ⟨3⟩ ⟨0⟩
      have hee1 : evm1s.executionEnv = I := by
        simp only [evm1s, evm0s, catCtorAfterWardsState, storageStore_executionEnv, initState]
      have hee2 : evm2s.executionEnv = I := by
        simp only [evm2s, catCtorAfterVatState, storageStore_executionEnv, hee1]
      have hAccountsVat : accountMapEquiv σVat evm2s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨3⟩)
            (EVM.word vat.val))
          hAccountsWards
        simpa [σVat, evm2s, catCtorAfterVatState, storageStore_accountMap,
          hee1, catCtorVatStored, hOldVat] using hbase
      have hAccountsLive : accountMapEquiv σLive evm3s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩ ⟨1⟩ hAccountsVat
        simpa [σLive, evm3s, catCtorAfterLiveState, storageStore_accountMap, hee2] using hbase
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, catCtorPostState] using
            catSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp only [catCtorAfterLiveState, catCtorAfterVatState, catCtorAfterWardsState,
          storageStore_createdAccounts, initState]
      · exact hAccountsLive
  · have hrd := catInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (catSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Cat
