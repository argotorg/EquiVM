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
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (vat gem : AccountAddress) :
    let evm0e := initState σ σ₀ g A I
    let evm0s := initState σ σ₀ g A I
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
    evm8e.accountMap = evm8s.accountMap := by
  intro evm0e evm0s evm1e evm1s evm2e evm2s evm3s evm4e evm4s evm5e evm5s
    evm6e evm6s evm7e evm7s evm8e evm8s
  have h1 : evm1e.accountMap = evm1s.accountMap := by
    simp [evm1e, evm1s, evm0e, evm0s, flapperCtorAfterBegState, initState,
      storageStore_accountMap]
  let packedS :=
    flapperCtorDefaultsSlot5Word
      (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
  let evm3sPacked :=
    Solm.EVM.storageStore evm1s evm1s.executionEnv.codeOwner ⟨5⟩ packedS
  have hPacked : evm2e.accountMap = evm3sPacked.accountMap := by
    have hEnv : evm1e.executionEnv = evm1s.executionEnv := by
      simp [evm1e, evm1s, evm0e, evm0s, flapperCtorAfterBegState,
        storageStore_executionEnv]
    have hLoad :
        Solm.EVM.storageLoad evm1e evm1e.executionEnv.codeOwner ⟨5⟩ =
          Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩ := by
      simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, h1, hEnv]
    have hval :
        flapperCtorDefaultsSlot5Word
            (Solm.EVM.storageLoad evm1e evm1e.executionEnv.codeOwner ⟨5⟩) =
          packedS := by
      simpa [packedS] using congrArg flapperCtorDefaultsSlot5Word hLoad
    simp only [evm2e, evm3sPacked, storageStore_accountMap]
    rw [show evm1e.executionEnv.codeOwner = evm1s.executionEnv.codeOwner from
      congrArg ExecutionEnv.codeOwner hEnv, h1, hval]
  have hPackedActual : evm3sPacked.accountMap = evm3s.accountMap := by
    cases hacc : evm1s.accountMap.get? evm1s.executionEnv.codeOwner with
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
        simpa [hPackedNoop, hTauNoop]
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
          sstoreAccountMap_self_update evm1s.accountMap
            evm1s.executionEnv.codeOwner ⟨5⟩
            (fileSetUint48Offset0Word
              (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨5⟩)
              flapperCtorTtlWord)
            packedS
        simpa [evm3sPacked, evm3s, evm2s, flapperCtorAfterTtlState,
          flapperCtorAfterTauState, storageStore_accountMap, storageStore_executionEnv,
          hTauVal'] using hbase
  have h2 : evm2e.accountMap = evm3s.accountMap := hPacked.trans hPackedActual
  have h3 : evm4e.accountMap = evm4s.accountMap := by
    have hEnv : evm2e.executionEnv = evm3s.executionEnv := by
      simp [evm2e, evm3s, evm2s, evm1e, evm1s, evm0e, evm0s,
        flapperCtorAfterKicksState, flapperCtorAfterTauState,
        flapperCtorAfterTtlState, flapperCtorAfterBegState,
        storageStore_executionEnv, initState]
    simp only [evm4e, evm4s, flapperCtorAfterKicksState, storageStore_accountMap]
    rw [show evm2e.executionEnv.codeOwner = evm3s.executionEnv.codeOwner from
      congrArg ExecutionEnv.codeOwner hEnv, h2]
  have h4 : evm5e.accountMap = evm5s.accountMap := by
    have hslotE : wardsSlot (.address evm4e.executionEnv.source) = flapperCtorCallerWardsSlot I := by
      simpa [evm4e, evm2e, evm1e, evm0e, flapperCtorAfterKicksState,
        flapperCtorAfterBegState, initState,
        storageStore_executionEnv] using flapperCtorCallerWardsSlot_eq I
    have hslotS : wardsSlot (.address evm4s.executionEnv.source) = flapperCtorCallerWardsSlot I := by
      simpa [evm4s, evm3s, evm2s, evm1s, evm0s, flapperCtorAfterKicksState,
        flapperCtorAfterTauState, flapperCtorAfterTtlState,
        flapperCtorAfterBegState, initState, storageStore_executionEnv] using
        flapperCtorCallerWardsSlot_eq I
    have hEnv : evm4e.executionEnv = evm4s.executionEnv := by
      simp [evm4e, evm4s, evm2e, evm3s, evm2s, evm1e, evm1s, evm0e, evm0s,
        flapperCtorAfterKicksState, flapperCtorAfterTauState,
        flapperCtorAfterTtlState, flapperCtorAfterBegState,
        storageStore_executionEnv, initState]
    simp only [evm5e, evm5s, flapperCtorAfterWardsState, storageStore_accountMap]
    rw [show evm4e.executionEnv.codeOwner = evm4s.executionEnv.codeOwner from
      congrArg ExecutionEnv.codeOwner hEnv, h3, hslotE, hslotS]
  have h5 : evm6e.accountMap = evm6s.accountMap := by
    have hEnv : evm5e.executionEnv = evm5s.executionEnv := by
      simp [evm5e, evm5s, evm4e, evm4s, evm2e, evm3s, evm1e, evm1s,
        evm0e, evm0s, evm2s, flapperCtorAfterWardsState, flapperCtorAfterKicksState,
        flapperCtorAfterTauState, flapperCtorAfterTtlState, flapperCtorAfterBegState,
        storageStore_executionEnv, initState]
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm5e evm5e.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm5s evm5s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val) := by
      have hLoad : Solm.EVM.storageLoad evm5e evm5e.executionEnv.codeOwner ⟨2⟩ =
          Solm.EVM.storageLoad evm5s evm5s.executionEnv.codeOwner ⟨2⟩ := by
        simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, h4, hEnv]
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word vat.val)) hLoad
    simp only [evm6e, evm6s, flapperCtorAfterVatState, storageStore_accountMap]
    have hval' :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm5e evm5s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm5s evm5s.executionEnv.codeOwner ⟨2⟩)
            (EVM.word vat.val) := by
      simpa [show evm5e.executionEnv.codeOwner = evm5s.executionEnv.codeOwner from
        congrArg ExecutionEnv.codeOwner hEnv] using hval
    rw [show evm5e.executionEnv.codeOwner = evm5s.executionEnv.codeOwner from
      congrArg ExecutionEnv.codeOwner hEnv, h4, hval']
  have h6 : evm7e.accountMap = evm7s.accountMap := by
    have hEnv : evm6e.executionEnv = evm6s.executionEnv := by
      simp [evm6e, evm6s, evm5e, evm5s, evm4e, evm4s, evm2e, evm3s,
        evm1e, evm1s, evm0e, evm0s, evm2s, flapperCtorAfterVatState,
        flapperCtorAfterWardsState, flapperCtorAfterKicksState,
        flapperCtorAfterTauState, flapperCtorAfterTtlState, flapperCtorAfterBegState,
        storageStore_executionEnv, initState]
    have hval :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm6e evm6e.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm6s evm6s.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) := by
      have hLoad : Solm.EVM.storageLoad evm6e evm6e.executionEnv.codeOwner ⟨3⟩ =
          Solm.EVM.storageLoad evm6s evm6s.executionEnv.codeOwner ⟨3⟩ := by
        simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage, h5, hEnv]
      exact congrArg (fun old => setAddressOffset0Word old (EVM.word gem.val)) hLoad
    simp only [evm7e, evm7s, flapperCtorAfterGemState, storageStore_accountMap]
    have hval' :
        setAddressOffset0Word
            (Solm.EVM.storageLoad evm6e evm6s.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) =
          setAddressOffset0Word
            (Solm.EVM.storageLoad evm6s evm6s.executionEnv.codeOwner ⟨3⟩)
            (EVM.word gem.val) := by
      simpa [show evm6e.executionEnv.codeOwner = evm6s.executionEnv.codeOwner from
        congrArg ExecutionEnv.codeOwner hEnv] using hval
    rw [show evm6e.executionEnv.codeOwner = evm6s.executionEnv.codeOwner from
      congrArg ExecutionEnv.codeOwner hEnv, h5, hval']
  have h7 : evm8e.accountMap = evm8s.accountMap := by
    have hEnv : evm7e.executionEnv = evm7s.executionEnv := by
      simp [evm7e, evm7s, evm6e, evm6s, evm5e, evm5s, evm4e, evm4s,
        evm2e, evm3s, evm2s, evm1e, evm1s, evm0e, evm0s,
        flapperCtorAfterGemState, flapperCtorAfterVatState,
        flapperCtorAfterWardsState, flapperCtorAfterKicksState,
        flapperCtorAfterTauState, flapperCtorAfterTtlState, flapperCtorAfterBegState,
        storageStore_executionEnv, initState]
    simp only [evm8e, evm8s, flapperCtorAfterLiveState, storageStore_accountMap]
    rw [show evm7e.executionEnv.codeOwner = evm7s.executionEnv.codeOwner from
      congrArg ExecutionEnv.codeOwner hEnv, h6]
  exact h7

set_option maxHeartbeats 2000000 in
theorem flapperConstructorCorrect :
    constructorEquivalence config flapperCreationBytecode contract flapperBytecode := by
  refine constructorEquivalence.intro ?_
  intro σ σ₀ g A I args deployedInitcode
    hdeploy hcode _hcalldata hperm
  rcases flapperCtorDeployment_shape hdeploy with ⟨vat, gem, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = flapperCtorCode vat gem := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := flapperInitcodeSuccess
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat gem hcodeCtor hperm hwv
    rcases hrd with hOOG | ⟨s, hX, hacc⟩
    · exact constructorEquivalenceFor.outOfGas
        (Xi_error_of_X (g := g) (by
          rw [← hcodeCtor] at hOOG
          simpa [Sat256.ofUInt256] using hOOG))
    · have hsuccess := Xi_success_of_X (g := g) (by
        rw [← hcodeCtor] at hX
        simpa [Sat256.ofUInt256] using hX)
      have hσ' : s.accountMap =
          flapperCtorFinalMap (flapperCtorAfterKicksMap σ I) I vat gem := hacc
      rw [hσ'] at hsuccess
      let evm0s :=
        initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1s := flapperCtorAfterBegState evm0s
      let evm2s := flapperCtorAfterTtlState evm1s
      let evm3s := flapperCtorAfterTauState evm2s
      let evm4s := flapperCtorAfterKicksState evm3s
      let evm5s := flapperCtorAfterWardsState evm4s
      let evm6s := flapperCtorAfterVatState evm5s vat
      let evm7s := flapperCtorAfterGemState evm6s gem
      let evm8s := flapperCtorAfterLiveState evm7s
      let evm0e :=
        initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1e := flapperCtorAfterBegState evm0e
      let evm2e := Solm.EVM.storageStore evm1e evm1e.executionEnv.codeOwner ⟨5⟩
        (flapperCtorDefaultsSlot5Word
          (Solm.EVM.storageLoad evm1e evm1e.executionEnv.codeOwner ⟨5⟩))
      let evm4e := flapperCtorAfterKicksState evm2e
      let evm5e := flapperCtorAfterWardsState evm4e
      let evm6e := flapperCtorAfterVatState evm5e vat
      let evm7e := flapperCtorAfterGemState evm6e gem
      let evm8e := flapperCtorAfterLiveState evm7e
      have hstate : evm8e.accountMap = evm8s.accountMap := by
        simpa [evm0e, evm0s, evm1e, evm1s, evm2e, evm2s, evm3s, evm4e, evm4s,
          evm5e, evm5s, evm6e, evm6s, evm7e, evm7s, evm8e, evm8s]
          using
            flapperCtorStateEquiv
              (σ := σ)  (σ₀ := σ₀)
              (A := A) (I := I) (g := Sat256.ofUInt256 g) vat gem
      have hMapE : evm8e.accountMap =
          flapperCtorFinalMap (flapperCtorAfterKicksMap σ I) I vat gem := by
        simp [-Std.ExtTreeMap.get?_eq_getElem?, evm8e, evm7e, evm6e, evm5e, evm4e, evm2e, evm1e, evm0e,
          flapperCtorFinalMap, flapperCtorAfterGemMap, flapperCtorAfterVatMap,
          flapperCtorAfterWardsMap, flapperCtorAfterKicksMap,
          flapperCtorAfterPackedDefaultsMap, flapperCtorAfterBegMap,
          flapperCtorAfterLiveState, flapperCtorAfterGemState,
          flapperCtorAfterVatState, flapperCtorAfterWardsState,
          flapperCtorAfterKicksState, flapperCtorAfterBegState, initState,
          storageStore_accountMap, storageStore_executionEnv, Solm.EVM.storageLoad,
          State.lookupAccount, Account.lookupStorage, solcSlotWord,
          flapperCtorCallerWardsSlot_eq]
      have hMapFinal :
          flapperCtorFinalMap (flapperCtorAfterKicksMap σ I) I vat gem =
            evm8s.accountMap := hMapE.symm.trans hstate
      refine constructorEquivalenceFor.execution hsuccess
        (by
          simpa [evm0s, evm1s, evm2s, evm3s, evm4s, evm5s, evm6s, evm7s, evm8s] using
            flapperSolmCtorExecSuccess
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) vat gem hwv)
        ?_
      exact ctorResultEquiv.success rfl rfl hMapFinal rfl
  · have hrd := flapperInitcodeNonpayableRevert
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) vat gem hcodeCtor hperm hwv
    rcases hrd.xiResult hcodeCtor with hOOG | ⟨g', out, hRev⟩
    · exact constructorEquivalenceFor.outOfGas (by simpa [Sat256.ofUInt256] using hOOG)
    · refine constructorEquivalenceFor.execution (by simpa [Sat256.ofUInt256] using hRev)
        (flapperSolmCtorExecReverts_nonpayable
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
          (g := g) vat gem hwv)
        ?_
      exact ctorResultEquiv.revert rfl rfl

end Benchmarks.Dss.Flapper
