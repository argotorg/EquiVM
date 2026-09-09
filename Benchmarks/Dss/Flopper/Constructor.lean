import Benchmarks.Dss.Flopper.ConstructorSource
import Benchmarks.Dss.Flopper.ConstructorTrace

/-!
# MakerDAO/Sky DSS Flopper constructor correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

set_option maxRecDepth 2000000

private theorem flopperCtorDefaultsSlot6Word_eq_source (old : UInt256) :
    flopperCtorDefaultsSlot6Word old =
      fileSetUint48Offset6Word (fileSetUint48Offset0Word old flopperCtorTtlWord)
        flopperCtorTauWord := by
  rw [flopperCtorDefaultsSlot6Word, fileSetUint48Offset0Word, fileSetUint48Offset6Word]
  rw [show UInt256.land flopperCtorTtlWord flopperUint48Mask = flopperCtorTtlWord
    by decide +native]
  rw [show UInt256.land flopperCtorTauWord flopperUint48Mask = flopperCtorTauWord
    by decide +native]
  rw [show UInt256.mul flopperCtorTauWord (UInt256.ofNat (2 ^ 48)) =
      UInt256.shiftLeft flopperCtorTauWord ⟨48⟩ by decide +native]
  rw [show fileUint48Offset6Mask = UInt256.shiftLeft flopperUint48Mask ⟨48⟩
    by decide +native]
  rw [u256_land_comm (UInt256.lnot (UInt256.shiftLeft flopperUint48Mask ⟨48⟩))
    (UInt256.lor (UInt256.land old (UInt256.lnot flopperUint48Mask)) flopperCtorTtlWord)]
  rw [u256_lor_comm]

private theorem flopperCtorStateEquiv
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let evm0e := initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I
    let evm0s := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
    let evm1e := flopperCtorAfterBegState evm0e
    let evm1s := flopperCtorAfterBegState evm0s
    let evm2e := flopperCtorAfterPadState evm1e
    let evm2s := flopperCtorAfterPadState evm1s
    let evm4e := Solm.EVM.storageStore evm2e evm2e.executionEnv.codeOwner ⟨6⟩
      (flopperCtorDefaultsSlot6Word
        (Solm.EVM.storageLoad evm2e evm2e.executionEnv.codeOwner ⟨6⟩))
    let evm3s := flopperCtorAfterTtlState evm2s
    let evm4s := flopperCtorAfterTauState evm3s
    let evm5e := flopperCtorAfterKicksState evm4e
    let evm5s := flopperCtorAfterKicksState evm4s
    let evm6e := flopperCtorAfterWardsState evm5e
    let evm6s := flopperCtorAfterWardsState evm5s
    let evm7e := flopperCtorAfterVatState evm6e vat
    let evm7s := flopperCtorAfterVatState evm6s vat
    let evm8e := flopperCtorAfterGemState evm7e gem
    let evm8s := flopperCtorAfterGemState evm7s gem
    let evm9e := flopperCtorAfterLiveState evm8e
    let evm9s := flopperCtorAfterLiveState evm8s
    EVMStateEquiv evm9e evm9s := by
  intro evm0e evm0s evm1e evm1s evm2e evm2s evm4e evm3s evm4s evm5e evm5s
    evm6e evm6s evm7e evm7s evm8e evm8s evm9e evm9s
  have h0 : EVMStateEquiv evm0e evm0s := by
    simpa [evm0e, evm0s] using EVMStateEquiv.initState (g := g) hAccounts
  have h1 : EVMStateEquiv evm1e evm1s := by
    simpa [evm1e, evm1s, evm0e, evm0s, flopperCtorAfterBegState, initState]
      using h0.storageStore_codeOwner ⟨4⟩ (show flopperCtorBegWord = flopperCtorBegWord by rfl)
  have h2 : EVMStateEquiv evm2e evm2s := by
    simpa [evm2e, evm2s, evm1e, evm1s, flopperCtorAfterPadState]
      using h1.storageStore_codeOwner ⟨5⟩ (show flopperCtorPadWord = flopperCtorPadWord by rfl)
  let packedS :=
    flopperCtorDefaultsSlot6Word
      (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨6⟩)
  let evm4sPacked :=
    Solm.EVM.storageStore evm2s evm2s.executionEnv.codeOwner ⟨6⟩ packedS
  have hPacked : EVMStateEquiv evm4e evm4sPacked := by
    have hval :
        flopperCtorDefaultsSlot6Word
            (Solm.EVM.storageLoad evm2e evm2e.executionEnv.codeOwner ⟨6⟩) =
          packedS := by
      simpa [packedS] using
        congrArg flopperCtorDefaultsSlot6Word (h2.storageLoad_codeOwner ⟨6⟩)
    simpa [evm4e, evm4sPacked] using h2.storageStore_codeOwner ⟨6⟩ hval
  have hPackedActual : accountMapEquiv evm4sPacked.accountMap evm4s.accountMap := by
    cases hacc : evm2s.accountMap.find? evm2s.executionEnv.codeOwner with
    | none =>
        have hPackedNoop : evm4sPacked = evm2s := by
          simpa [evm4sPacked, packedS] using
            storageStore_absent evm2s evm2s.executionEnv.codeOwner hacc ⟨6⟩ packedS
        have hTtlNoop : evm3s = evm2s := by
          simpa [evm3s, flopperCtorAfterTtlState] using
            storageStore_absent evm2s evm2s.executionEnv.codeOwner hacc ⟨6⟩
              (fileSetUint48Offset0Word
                (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨6⟩)
                flopperCtorTtlWord)
        have hTauNoop : evm4s = evm2s := by
          simpa [evm4s, flopperCtorAfterTauState, hTtlNoop] using
            storageStore_absent evm2s evm2s.executionEnv.codeOwner hacc ⟨6⟩
              (fileSetUint48Offset6Word
                (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨6⟩)
                flopperCtorTauWord)
        simpa [hPackedNoop, hTauNoop] using accountMapEquiv_refl evm2s.accountMap
    | some acc =>
        have hTtlLoad :
            Solm.EVM.storageLoad evm3s evm3s.executionEnv.codeOwner ⟨6⟩ =
              fileSetUint48Offset0Word
                (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨6⟩)
                flopperCtorTtlWord := by
          simpa [evm3s, flopperCtorAfterTtlState, storageStore_executionEnv] using
            storageLoad_storageStore_same_present evm2s evm2s.executionEnv.codeOwner hacc
              ⟨6⟩
              (fileSetUint48Offset0Word
                (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨6⟩)
                flopperCtorTtlWord)
        have hTauVal :
            fileSetUint48Offset6Word
                (Solm.EVM.storageLoad evm3s evm3s.executionEnv.codeOwner ⟨6⟩)
                flopperCtorTauWord =
              packedS := by
          rw [hTtlLoad]
          exact (flopperCtorDefaultsSlot6Word_eq_source
            (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨6⟩)).symm
        have hTauVal' :
            fileSetUint48Offset6Word
                (Solm.EVM.storageLoad
                  (Solm.EVM.storageStore evm2s evm2s.executionEnv.codeOwner ⟨6⟩
                    (fileSetUint48Offset0Word
                      (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨6⟩)
                      flopperCtorTtlWord))
                  evm2s.executionEnv.codeOwner ⟨6⟩)
                flopperCtorTauWord =
              packedS := by
          simpa [evm3s, flopperCtorAfterTtlState, storageStore_executionEnv] using hTauVal
        have hbase :=
          accountMapEquiv_sstoreAccountMap_self_update evm2s.accountMap
            evm2s.executionEnv.codeOwner ⟨6⟩
            (fileSetUint48Offset0Word
              (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨6⟩)
              flopperCtorTtlWord)
            packedS
        simpa [evm4sPacked, evm4s, evm3s, flopperCtorAfterTtlState,
          flopperCtorAfterTauState, storageStore_accountMap, storageStore_executionEnv,
          hTauVal'] using hbase
  have h3 : EVMStateEquiv evm4e evm4s := by
    refine ⟨?_, ?_, accountMapEquiv.trans hPacked.accountMap hPackedActual⟩
    · simpa [evm4sPacked, evm4s, evm3s, flopperCtorAfterTtlState,
        flopperCtorAfterTauState, storageStore_executionEnv] using hPacked.executionEnv
    · simpa [evm4sPacked, evm4s, evm3s, flopperCtorAfterTtlState,
        flopperCtorAfterTauState, storageStore_createdAccounts] using hPacked.createdAccounts
  have h4 : EVMStateEquiv evm5e evm5s := by
    simpa [evm5e, evm5s, evm4e, evm4s, flopperCtorAfterKicksState]
      using h3.storageStore_codeOwner ⟨7⟩ (show (⟨0⟩ : UInt256) = ⟨0⟩ by rfl)
  have h5 : EVMStateEquiv evm6e evm6s := by
    have hslotE : wardsSlot (.address evm5e.executionEnv.source) = flopperCtorCallerWardsSlot I := by
      simpa [evm5e, evm4e, evm2e, evm1e, evm0e, flopperCtorAfterKicksState,
        flopperCtorAfterPadState, flopperCtorAfterBegState, initState,
        storageStore_executionEnv] using flopperCtorCallerWardsSlot_eq I
    have hslotS : wardsSlot (.address evm5s.executionEnv.source) = flopperCtorCallerWardsSlot I := by
      simpa [evm5s, evm4s, evm3s, evm2s, evm1s, evm0s, flopperCtorAfterKicksState,
        flopperCtorAfterTauState, flopperCtorAfterTtlState, flopperCtorAfterPadState,
        flopperCtorAfterBegState, initState, storageStore_executionEnv] using
        flopperCtorCallerWardsSlot_eq I
    simpa [evm6e, evm6s, evm5e, evm5s, flopperCtorAfterWardsState, hslotE, hslotS]
      using h4.storageStore_codeOwner (flopperCtorCallerWardsSlot I)
        (show (⟨1⟩ : UInt256) = ⟨1⟩ by rfl)
  have h6 : EVMStateEquiv evm7e evm7s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm6e evm6e.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm6s evm6s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word vat.val))
        (h5.storageLoad_codeOwner ⟨2⟩)
    simpa [evm7e, evm7s, flopperCtorAfterVatState] using h5.storageStore_codeOwner ⟨2⟩ hval
  have h7 : EVMStateEquiv evm8e evm8s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm7e evm7e.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm7s evm7s.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word gem.val))
        (h6.storageLoad_codeOwner ⟨3⟩)
    simpa [evm8e, evm8s, flopperCtorAfterGemState] using h6.storageStore_codeOwner ⟨3⟩ hval
  have h8 : EVMStateEquiv evm9e evm9s := by
    simpa [evm9e, evm9s, flopperCtorAfterLiveState]
      using h7.storageStore_codeOwner ⟨8⟩ (show (⟨1⟩ : UInt256) = ⟨1⟩ by rfl)
  exact h8

set_option maxHeartbeats 2000000 in
theorem flopperConstructorCorrect :
    constructorEquivalence config flopperCreationBytecode contract flopperBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases flopperCtorDeployment_shape hdeploy with ⟨vat, gem, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = flopperCtorCode vat gem := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := flopperInitcodeSuccess
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat gem hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hcA : s.createdAccounts = createdAccounts := congrArg Prod.fst hacc
      have hσ' : s.accountMap =
          flopperCtorFinalMap (flopperCtorAfterKicksMap σ_evm I) I vat gem := by
        simpa using congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := flopperCtorAfterBegState evm0s
      let evm2s := flopperCtorAfterPadState evm1s
      let evm3s := flopperCtorAfterTtlState evm2s
      let evm4s := flopperCtorAfterTauState evm3s
      let evm5s := flopperCtorAfterKicksState evm4s
      let evm6s := flopperCtorAfterWardsState evm5s
      let evm7s := flopperCtorAfterVatState evm6s vat
      let evm8s := flopperCtorAfterGemState evm7s gem
      let evm9s := flopperCtorAfterLiveState evm8s
      let evm0e :=
        initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ (Sat256.ofUInt256 g) A I
      let evm1e := flopperCtorAfterBegState evm0e
      let evm2e := flopperCtorAfterPadState evm1e
      let evm4e := Solm.EVM.storageStore evm2e evm2e.executionEnv.codeOwner ⟨6⟩
        (flopperCtorDefaultsSlot6Word
          (Solm.EVM.storageLoad evm2e evm2e.executionEnv.codeOwner ⟨6⟩))
      let evm5e := flopperCtorAfterKicksState evm4e
      let evm6e := flopperCtorAfterWardsState evm5e
      let evm7e := flopperCtorAfterVatState evm6e vat
      let evm8e := flopperCtorAfterGemState evm7e gem
      let evm9e := flopperCtorAfterLiveState evm8e
      have hstate : EVMStateEquiv evm9e evm9s := by
        simpa [evm0e, evm0s, evm1e, evm1s, evm2e, evm2s, evm3s, evm4e, evm4s,
          evm5e, evm5s, evm6e, evm6s, evm7e, evm7s, evm8e, evm8s, evm9e, evm9s]
          using
            flopperCtorStateEquiv
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) vat gem hAccounts
      have hslot : wardsSlot (.address I.source) = flopperCtorCallerWardsSlot I :=
        flopperCtorCallerWardsSlot_eq I
      have hAccountsFinal :
          accountMapEquiv (flopperCtorFinalMap (flopperCtorAfterKicksMap σ_evm I) I vat gem)
            evm9s.accountMap := by
        simpa [evm9e, evm8e, evm7e, evm6e, evm5e, evm4e, evm2e, evm1e, evm0e,
          evm9s, evm8s, evm7s, evm6s, evm5s, evm4s, evm3s, evm2s, evm1s, evm0s,
          flopperCtorFinalMap, flopperCtorAfterGemMap, flopperCtorAfterVatMap,
          flopperCtorAfterWardsMap, flopperCtorAfterKicksMap,
          flopperCtorAfterPackedDefaultsMap, flopperCtorAfterPadMap,
          flopperCtorAfterBegMap, flopperCtorAfterLiveState, flopperCtorAfterGemState,
          flopperCtorAfterVatState, flopperCtorAfterWardsState, flopperCtorAfterKicksState,
          flopperCtorAfterTauState, flopperCtorAfterTtlState, flopperCtorAfterPadState,
          flopperCtorAfterBegState, initState, storageStore_accountMap,
          storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage, solcSlotWord, hslot] using hstate.accountMap
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s, evm5s, evm6s, evm7s, evm8s,
            evm9s] using
            flopperSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat gem hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [evm9s, evm8s, evm7s, evm6s, evm5s, evm4s, evm3s, evm2s, evm1s,
          evm0s, flopperCtorAfterLiveState, flopperCtorAfterGemState,
          flopperCtorAfterVatState, flopperCtorAfterWardsState, flopperCtorAfterKicksState,
          flopperCtorAfterTauState, flopperCtorAfterTtlState, flopperCtorAfterPadState,
          flopperCtorAfterBegState, storageStore_createdAccounts, initState]
      · exact hAccountsFinal
  · have hrd := flopperInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat gem hcodeCtor hperm hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (flopperSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat gem hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Flopper
