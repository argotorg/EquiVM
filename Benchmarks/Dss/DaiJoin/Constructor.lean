import Benchmarks.Dss.DaiJoin.ConstructorSource
import Benchmarks.Dss.DaiJoin.ConstructorTraceReturn

/-!
# MakerDAO/Sky DSS DaiJoin constructor correctness

The optimized creation bytecode, deployed runtime bytecode, and Solm constructor specification are
connected by the constructor-equivalence proof.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem daiJoinConstructorCorrect :
    constructorEquivalence config daiJoinCreationBytecode contract daiJoinBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases daiJoinCtorDeployment_shape hdeploy with ⟨vat, dai, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = daiJoinCtorCode vat dai := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := daiJoinInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat dai hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ_evm (daiJoinCtorCallerWardsSlot I) ⟨1⟩
      let σLive := sstoreAccountMap I.codeOwner σWards ⟨3⟩ ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σLive ⟨1⟩ (daiJoinCtorVatStored σLive I vat)
      let σDai := sstoreAccountMap I.codeOwner σVat ⟨2⟩ (daiJoinCtorDaiStored σVat I dai)
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap = σDai := by
        simpa [σWards, σLive, σVat, σDai] using congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := daiJoinCtorAfterWardsState evm0s
      let evm2s := daiJoinCtorAfterLiveState evm1s
      let evm3s := daiJoinCtorAfterVatState evm2s vat
      let evm4s := daiJoinCtorAfterDaiState evm3s dai
      have hslot : wardsSlot (.address I.source) = daiJoinCtorCallerWardsSlot I :=
        daiJoinCtorCallerWardsSlot_eq I
      have hAccountsWards : accountMapEquiv σWards evm1s.accountMap := by
        simpa [σWards, evm1s, evm0s, daiJoinCtorAfterWardsState, initState,
          storageStore_accountMap, storageStore_executionEnv, hslot] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (daiJoinCtorCallerWardsSlot I) ⟨1⟩
            hAccounts
      have hAccountsLive : accountMapEquiv σLive evm2s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ ⟨1⟩ hAccountsWards
        simpa [σLive, evm2s, evm1s, evm0s, daiJoinCtorAfterLiveState,
          daiJoinCtorAfterWardsState, initState, storageStore_accountMap,
          storageStore_executionEnv] using hbase
      have hOldVat :
          solcSlotWord σLive I ⟨1⟩ =
            Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨1⟩ := by
        simpa [evm2s, evm1s, evm0s, daiJoinCtorAfterLiveState,
          daiJoinCtorAfterWardsState, initState, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord, storageStore_executionEnv] using
          accountMapEquiv_storage_findD hAccountsLive I.codeOwner ⟨1⟩ ⟨0⟩
      have hAccountsVat : accountMapEquiv σVat evm3s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨1⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨1⟩)
            (EVM.word vat.val))
          hAccountsLive
        simpa [σVat, σLive, evm3s, evm2s, evm1s, evm0s, daiJoinCtorAfterVatState,
          daiJoinCtorAfterLiveState, daiJoinCtorAfterWardsState, initState,
          storageStore_accountMap, storageStore_executionEnv, daiJoinCtorVatStored, hOldVat]
          using hbase
      have hOldDai :
          solcSlotWord σVat I ⟨2⟩ =
            Solm.EVM.storageLoad evm3s evm3s.executionEnv.codeOwner ⟨2⟩ := by
        simpa [evm3s, evm2s, evm1s, evm0s, daiJoinCtorAfterVatState,
          daiJoinCtorAfterLiveState, daiJoinCtorAfterWardsState, initState,
          Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, solcSlotWord,
          storageStore_executionEnv] using
          accountMapEquiv_storage_findD hAccountsVat I.codeOwner ⟨2⟩ ⟨0⟩
      have hAccountsDai : accountMapEquiv σDai evm4s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨2⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm3s evm3s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word dai.val))
          hAccountsVat
        simpa [σDai, σVat, evm4s, evm3s, evm2s, evm1s, evm0s,
          daiJoinCtorAfterDaiState, daiJoinCtorAfterVatState, daiJoinCtorAfterLiveState,
          daiJoinCtorAfterWardsState, initState, storageStore_accountMap,
          storageStore_executionEnv, daiJoinCtorDaiStored, hOldDai]
          using hbase
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s] using
            daiJoinSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat dai hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [daiJoinCtorAfterDaiState, daiJoinCtorAfterVatState, daiJoinCtorAfterLiveState,
          daiJoinCtorAfterWardsState, storageStore_createdAccounts, initState]
      · simpa [evm4s] using hAccountsDai
  · have hrd := daiJoinInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat dai hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (daiJoinSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat dai hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.DaiJoin
