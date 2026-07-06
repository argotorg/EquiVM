import Benchmarks.Dss.Pot.ConstructorSource
import Benchmarks.Dss.Pot.ConstructorTraceReturn

/-!
# MakerDAO/Sky DSS Pot constructor correctness

The Pot constructor stores six slots — `wards[sender] = 1`, `vat = vat_` (slot 5), `dsr = ONE`,
`chi = ONE`, `rho = now`, `live = 1` — matching the optimized creation bytecode's store order.  The
EVM trace lives in `ConstructorTrace*`, the Solm source semantics in `ConstructorSource`, and this
file assembles the two through the account-map-equivalence chain.
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem potConstructorCorrect :
    constructorEquivalence config potCreationBytecode contract potBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases potCtorDeployment_shape hdeploy with ⟨vat, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = potCtorCode vat := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := potInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · let σWards := sstoreAccountMap I.codeOwner σ_evm (potCtorCallerWardsSlot I) ⟨1⟩
      let σVat := sstoreAccountMap I.codeOwner σWards ⟨5⟩ (potCtorVatStored σWards I vat)
      let σDsr := sstoreAccountMap I.codeOwner σVat ⟨3⟩ potCtorOne
      let σChi := sstoreAccountMap I.codeOwner σDsr ⟨4⟩ potCtorOne
      let σRho := sstoreAccountMap I.codeOwner σChi ⟨7⟩ (UInt256.ofNat I.header.timestamp)
      let σLive := sstoreAccountMap I.codeOwner σRho ⟨8⟩ ⟨1⟩
      have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap = σLive := by
        simpa [σWards, σVat, σDsr, σChi, σRho, σLive] using congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := potCtorAfterWardsState evm0s
      let evm2s := potCtorAfterVatState evm1s vat
      let evm3s := potCtorAfterDsrState evm2s
      let evm4s := potCtorAfterChiState evm3s
      let evm5s := potCtorAfterRhoState evm4s
      let evm6s := potCtorAfterLiveState evm5s
      have hslot : wardsSlot (.address I.source) = potCtorCallerWardsSlot I :=
        potCtorCallerWardsSlot_eq I
      have hAccountsWards : accountMapEquiv σWards evm1s.accountMap := by
        simpa [σWards, evm1s, evm0s, potCtorAfterWardsState, initState,
          storageStore_accountMap, storageStore_executionEnv, hslot] using
          accountMapEquiv_sstoreAccountMap I.codeOwner (potCtorCallerWardsSlot I) ⟨1⟩
            hAccounts
      have hOldVat :
          solcSlotWord σWards I ⟨5⟩ =
            Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩ := by
        simpa [evm1s, evm0s, potCtorAfterWardsState, initState, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord, storageStore_executionEnv] using
          accountMapEquiv_storage_findD hAccountsWards I.codeOwner ⟨5⟩ ⟨0⟩
      have hee1 : evm1s.executionEnv = I := by
        simp only [evm1s, evm0s, potCtorAfterWardsState, storageStore_executionEnv, initState]
      have hee2 : evm2s.executionEnv = I := by
        simp only [evm2s, potCtorAfterVatState, storageStore_executionEnv, hee1]
      have hee3 : evm3s.executionEnv = I := by
        simp only [evm3s, potCtorAfterDsrState, storageStore_executionEnv, hee2]
      have hee4 : evm4s.executionEnv = I := by
        simp only [evm4s, potCtorAfterChiState, storageStore_executionEnv, hee3]
      have hee5 : evm5s.executionEnv = I := by
        simp only [evm5s, potCtorAfterRhoState, storageStore_executionEnv, hee4]
      have hAccountsVat : accountMapEquiv σVat evm2s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨5⟩
          (setAddressOffset0Word
            (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
            (EVM.word vat.val))
          hAccountsWards
        simpa [σVat, evm2s, potCtorAfterVatState, storageStore_accountMap,
          hee1, potCtorVatStored, hOldVat] using hbase
      have hAccountsDsr : accountMapEquiv σDsr evm3s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨3⟩ potCtorOne hAccountsVat
        simpa [σDsr, evm3s, potCtorAfterDsrState, storageStore_accountMap, hee2] using hbase
      have hAccountsChi : accountMapEquiv σChi evm4s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨4⟩ potCtorOne hAccountsDsr
        simpa [σChi, evm4s, potCtorAfterChiState, storageStore_accountMap, hee3] using hbase
      have hAccountsRho : accountMapEquiv σRho evm5s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨7⟩
          (UInt256.ofNat I.header.timestamp) hAccountsChi
        simpa [σRho, evm5s, potCtorAfterRhoState, storageStore_accountMap, hee4] using hbase
      have hAccountsLive : accountMapEquiv σLive evm6s.accountMap := by
        have hbase := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨8⟩ ⟨1⟩ hAccountsRho
        simpa [σLive, evm6s, potCtorAfterLiveState, storageStore_accountMap, hee5] using hbase
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s, evm5s, evm6s, potCtorPostState] using
            potSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp only [potCtorAfterLiveState, potCtorAfterRhoState, potCtorAfterChiState,
          potCtorAfterDsrState, potCtorAfterVatState, potCtorAfterWardsState,
          storageStore_createdAccounts, initState]
      · exact hAccountsLive
  · have hrd := potInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat hcodeCtor hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (potSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Pot
