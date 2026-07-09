import Benchmarks.Dss.Flapper.ConstructorSource
import Benchmarks.Dss.Flapper.ConstructorTrace

/-!
# MakerDAO/Sky DSS Flapper constructor correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flapper

set_option maxRecDepth 2000000

private theorem flapperCtorDefaultsSlot5Word_eq_source (old : UInt256) :
    flapperCtorDefaultsSlot5Word old =
      fileSetUint48Offset6Word (fileSetUint48Offset0Word old flapperCtorTtlWord)
        flapperCtorTauWord := by
  rw [flapperCtorDefaultsSlot5Word, fileSetUint48Offset0Word, fileSetUint48Offset6Word]
  rw [show UInt256.land flapperCtorTtlWord flapperUint48Mask = flapperCtorTtlWord
    by native_decide]
  rw [show UInt256.land flapperCtorTauWord flapperUint48Mask = flapperCtorTauWord
    by native_decide]
  rw [show UInt256.mul flapperCtorTauWord (UInt256.ofNat (2 ^ 48)) =
      UInt256.shiftLeft flapperCtorTauWord ⟨48⟩ by native_decide]
  rw [show fileUint48Offset6Mask = UInt256.shiftLeft flapperUint48Mask ⟨48⟩
    by native_decide]
  rw [u256_land_comm (UInt256.lnot (UInt256.shiftLeft flapperUint48Mask ⟨48⟩))
    (UInt256.lor (UInt256.land old (UInt256.lnot flapperUint48Mask)) flapperCtorTtlWord)]
  rw [u256_lor_comm]

private theorem flapperCtorStateEquiv
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ_evm σ_solm σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress)
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    let evm0e := initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ g A I
    let evm0s := initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ g A I
    let evm1e := flapperCtorAfterBegState evm0e
    let evm1s := flapperCtorAfterBegState evm0s
    let evm2e := Solm.EVM.storageStore evm1e evm1e.executionEnv.codeOwner ⟨5⟩
      (flapperCtorDefaultsSlot5Word
        (Solm.EVM.storageLoad evm1e evm1e.executionEnv.codeOwner ⟨5⟩))
    let evm2s := flapperCtorAfterTtlState evm1s
    let evm3s := flapperCtorAfterTauState evm2s
    let evm4e := flapperCtorAfterKicksState evm2e
    let evm4s := flapperCtorAfterKicksState evm3s
    let evm5e := flapperCtorAfterWardsState evm4e
    let evm5s := flapperCtorAfterWardsState evm4s
    let evm6e := flapperCtorAfterVatState evm5e vat
    let evm6s := flapperCtorAfterVatState evm5s vat
    let evm7e := flapperCtorAfterGemState evm6e gem
    let evm7s := flapperCtorAfterGemState evm6s gem
    let evm8e := flapperCtorAfterLiveState evm7e
    let evm8s := flapperCtorAfterLiveState evm7s
    EVMStateEquiv evm8e evm8s := by
  intro evm0e evm0s evm1e evm1s evm2e evm2s evm3s evm4e evm4s evm5e evm5s
    evm6e evm6s evm7e evm7s evm8e evm8s
  have h0 : EVMStateEquiv evm0e evm0s := by
    simpa [evm0e, evm0s] using EVMStateEquiv.initState (g := g) hAccounts
  have h1 : EVMStateEquiv evm1e evm1s := by
    simpa [evm1e, evm1s, evm0e, evm0s, flapperCtorAfterBegState, initState]
      using h0.storageStore_codeOwner ⟨4⟩ (show flapperCtorBegWord = flapperCtorBegWord by rfl)
  let packedS :=
    flapperCtorDefaultsSlot5Word
      (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
  let evm3sPacked :=
    Solm.EVM.storageStore evm1s evm1s.executionEnv.codeOwner ⟨5⟩ packedS
  have hPacked : EVMStateEquiv evm2e evm3sPacked := by
    have hval :
        flapperCtorDefaultsSlot5Word
            (Solm.EVM.storageLoad evm1e evm1e.executionEnv.codeOwner ⟨5⟩) =
          packedS := by
      simpa [packedS] using
        congrArg flapperCtorDefaultsSlot5Word (h1.storageLoad_codeOwner ⟨5⟩)
    simpa [evm2e, evm3sPacked] using h1.storageStore_codeOwner ⟨5⟩ hval
  have hPackedActual : accountMapEquiv evm3sPacked.accountMap evm3s.accountMap := by
    cases hacc : evm1s.accountMap.find? evm1s.executionEnv.codeOwner with
    | none =>
        have hPackedNoop : evm3sPacked = evm1s := by
          simpa [evm3sPacked, packedS] using
            storageStore_absent evm1s evm1s.executionEnv.codeOwner hacc ⟨5⟩ packedS
        have hTtlNoop : evm2s = evm1s := by
          simpa [evm2s, flapperCtorAfterTtlState] using
            storageStore_absent evm1s evm1s.executionEnv.codeOwner hacc ⟨5⟩
              (fileSetUint48Offset0Word
                (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
                flapperCtorTtlWord)
        have hTauNoop : evm3s = evm1s := by
          simpa [evm3s, flapperCtorAfterTauState, hTtlNoop] using
            storageStore_absent evm1s evm1s.executionEnv.codeOwner hacc ⟨5⟩
              (fileSetUint48Offset6Word
                (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
                flapperCtorTauWord)
        simpa [hPackedNoop, hTauNoop] using accountMapEquiv_refl evm1s.accountMap
    | some acc =>
        have hTtlLoad :
            Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨5⟩ =
              fileSetUint48Offset0Word
                (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
                flapperCtorTtlWord := by
          simpa [evm2s, flapperCtorAfterTtlState, storageStore_executionEnv] using
            storageLoad_storageStore_same_present evm1s evm1s.executionEnv.codeOwner hacc
              ⟨5⟩
              (fileSetUint48Offset0Word
                (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
                flapperCtorTtlWord)
        have hTauVal :
            fileSetUint48Offset6Word
                (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨5⟩)
                flapperCtorTauWord =
              packedS := by
          rw [hTtlLoad]
          exact (flapperCtorDefaultsSlot5Word_eq_source
            (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)).symm
        have hTauVal' :
            fileSetUint48Offset6Word
                (Solm.EVM.storageLoad
                  (Solm.EVM.storageStore evm1s evm1s.executionEnv.codeOwner ⟨5⟩
                    (fileSetUint48Offset0Word
                      (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
                      flapperCtorTtlWord))
                  evm1s.executionEnv.codeOwner ⟨5⟩)
                flapperCtorTauWord =
              packedS := by
          simpa [evm2s, flapperCtorAfterTtlState, storageStore_executionEnv] using hTauVal
        have hbase :=
          accountMapEquiv_sstoreAccountMap_self_update evm1s.accountMap
            evm1s.executionEnv.codeOwner ⟨5⟩
            (fileSetUint48Offset0Word
              (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
              flapperCtorTtlWord)
            packedS
        simpa [evm3sPacked, evm3s, evm2s, flapperCtorAfterTtlState,
          flapperCtorAfterTauState, storageStore_accountMap, storageStore_executionEnv,
          hTauVal'] using hbase
  have h2 : EVMStateEquiv evm2e evm3s := by
    refine ⟨?_, ?_, accountMapEquiv.trans hPacked.accountMap hPackedActual⟩
    · simpa [evm3sPacked, evm3s, evm2s, flapperCtorAfterTtlState,
        flapperCtorAfterTauState, storageStore_executionEnv] using hPacked.executionEnv
    · simpa [evm3sPacked, evm3s, evm2s, flapperCtorAfterTtlState,
        flapperCtorAfterTauState, storageStore_createdAccounts] using hPacked.createdAccounts
  have h3 : EVMStateEquiv evm4e evm4s := by
    simpa [evm4e, evm4s, evm2e, evm3s, flapperCtorAfterKicksState]
      using h2.storageStore_codeOwner ⟨6⟩ (show (⟨0⟩ : UInt256) = ⟨0⟩ by rfl)
  have h4 : EVMStateEquiv evm5e evm5s := by
    have hslotE : wardsSlot (.address evm4e.executionEnv.source) = flapperCtorCallerWardsSlot I := by
      simpa [evm4e, evm2e, evm1e, evm0e, flapperCtorAfterKicksState,
        flapperCtorAfterBegState, initState,
        storageStore_executionEnv] using flapperCtorCallerWardsSlot_eq I
    have hslotS : wardsSlot (.address evm4s.executionEnv.source) = flapperCtorCallerWardsSlot I := by
      simpa [evm4s, evm3s, evm2s, evm1s, evm0s, flapperCtorAfterKicksState,
        flapperCtorAfterTauState, flapperCtorAfterTtlState,
        flapperCtorAfterBegState, initState, storageStore_executionEnv] using
        flapperCtorCallerWardsSlot_eq I
    simpa [evm5e, evm5s, evm4e, evm4s, flapperCtorAfterWardsState, hslotE, hslotS]
      using h3.storageStore_codeOwner (flapperCtorCallerWardsSlot I)
        (show (⟨1⟩ : UInt256) = ⟨1⟩ by rfl)
  have h5 : EVMStateEquiv evm6e evm6s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm5e evm5e.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm5s evm5s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word vat.val))
        (h4.storageLoad_codeOwner ⟨2⟩)
    simpa [evm6e, evm6s, flapperCtorAfterVatState] using h4.storageStore_codeOwner ⟨2⟩ hval
  have h6 : EVMStateEquiv evm7e evm7s := by
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm6e evm6e.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm6s evm6s.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) := by
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word gem.val))
        (h5.storageLoad_codeOwner ⟨3⟩)
    simpa [evm7e, evm7s, flapperCtorAfterGemState] using h5.storageStore_codeOwner ⟨3⟩ hval
  have h7 : EVMStateEquiv evm8e evm8s := by
    simpa [evm8e, evm8s, flapperCtorAfterLiveState]
      using h6.storageStore_codeOwner ⟨7⟩ (show (⟨1⟩ : UInt256) = ⟨1⟩ by rfl)
  exact h7

set_option maxHeartbeats 2000000 in
theorem flapperConstructorCorrect :
    constructorEquivalence config flapperCreationBytecode contract flapperBytecode := by
  refine constructorEquivalence.intro ?_
  intro createdAccounts genesisBlockHeader blocks σ_evm σ_solm σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm hAccounts
  rcases flapperCtorDeployment_shape hdeploy with ⟨vat, gem, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = flapperCtorCode vat gem := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := flapperInitcodeSuccess
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
          flapperCtorFinalMap (flapperCtorAfterKicksMap σ_evm I) I vat gem := by
        simpa using congrArg Prod.snd hacc
      rw [hcA, hσ'] at hsuccess
      let evm0s :=
        initState createdAccounts genesisBlockHeader blocks σ_solm σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := flapperCtorAfterBegState evm0s
      let evm2s := flapperCtorAfterTtlState evm1s
      let evm3s := flapperCtorAfterTauState evm2s
      let evm4s := flapperCtorAfterKicksState evm3s
      let evm5s := flapperCtorAfterWardsState evm4s
      let evm6s := flapperCtorAfterVatState evm5s vat
      let evm7s := flapperCtorAfterGemState evm6s gem
      let evm8s := flapperCtorAfterLiveState evm7s
      let evm0e :=
        initState createdAccounts genesisBlockHeader blocks σ_evm σ₀ (Sat256.ofUInt256 g) A I
      let evm1e := flapperCtorAfterBegState evm0e
      let evm2e := Solm.EVM.storageStore evm1e evm1e.executionEnv.codeOwner ⟨5⟩
        (flapperCtorDefaultsSlot5Word
          (Solm.EVM.storageLoad evm1e evm1e.executionEnv.codeOwner ⟨5⟩))
      let evm4e := flapperCtorAfterKicksState evm2e
      let evm5e := flapperCtorAfterWardsState evm4e
      let evm6e := flapperCtorAfterVatState evm5e vat
      let evm7e := flapperCtorAfterGemState evm6e gem
      let evm8e := flapperCtorAfterLiveState evm7e
      have hstate : EVMStateEquiv evm8e evm8s := by
        simpa [evm0e, evm0s, evm1e, evm1s, evm2e, evm2s, evm3s, evm4e, evm4s,
          evm5e, evm5s, evm6e, evm6s, evm7e, evm7s, evm8e, evm8s]
          using
            flapperCtorStateEquiv
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ_evm := σ_evm) (σ_solm := σ_solm) (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) vat gem hAccounts
      have hslot : wardsSlot (.address I.source) = flapperCtorCallerWardsSlot I :=
        flapperCtorCallerWardsSlot_eq I
      have hAccountsFinal :
          accountMapEquiv (flapperCtorFinalMap (flapperCtorAfterKicksMap σ_evm I) I vat gem)
            evm8s.accountMap := by
        simpa [evm8e, evm7e, evm6e, evm5e, evm4e, evm2e, evm1e, evm0e,
          evm8s, evm7s, evm6s, evm5s, evm4s, evm3s, evm2s, evm1s, evm0s,
          flapperCtorFinalMap, flapperCtorAfterGemMap, flapperCtorAfterVatMap,
          flapperCtorAfterWardsMap, flapperCtorAfterKicksMap,
          flapperCtorAfterPackedDefaultsMap,
          flapperCtorAfterBegMap, flapperCtorAfterLiveState, flapperCtorAfterGemState,
          flapperCtorAfterVatState, flapperCtorAfterWardsState, flapperCtorAfterKicksState,
          flapperCtorAfterTauState, flapperCtorAfterTtlState,
          flapperCtorAfterBegState, initState, storageStore_accountMap,
          storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage, solcSlotWord, hslot] using hstate.accountMap
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s, evm5s, evm6s, evm7s, evm8s] using
            flapperSolmCtorExecSuccess
              (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
              (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat gem hwv)
        ?_
      refine ctorResultEquiv.success rfl rfl ?_ ?_ rfl
      · simp [evm8s, evm7s, evm6s, evm5s, evm4s, evm3s, evm2s, evm1s,
          evm0s, flapperCtorAfterLiveState, flapperCtorAfterGemState,
          flapperCtorAfterVatState, flapperCtorAfterWardsState, flapperCtorAfterKicksState,
          flapperCtorAfterTauState, flapperCtorAfterTtlState,
          flapperCtorAfterBegState, storageStore_createdAccounts, initState]
      · exact hAccountsFinal
  · have hrd := flapperInitcodeNonpayableRevert
      (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
      (blocks := blocks) (σ := σ_evm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat gem hcodeCtor hperm hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (flapperSolmCtorExecReverts_nonpayable
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat gem hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Flapper
