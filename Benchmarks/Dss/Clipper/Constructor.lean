import Benchmarks.Dss.Clipper.ConstructorSource
import Benchmarks.Dss.Clipper.ConstructorTrace
import Solm.Refine
import Reasoning.Immutables

/-!
# MakerDAO/Sky DSS Clipper constructor correctness
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables
open Reasoning.Immutables (wordsOf wordsOf_of_get Layout.deployed)

namespace Benchmarks.Dss.Clipper

set_option maxRecDepth 2000000

private theorem clipperCtorStateEquiv
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : Sat256}
    (spotter dog : AccountAddress) :
    let evm0e := initState σ σ₀ g A I
    let evm0s := initState σ σ₀ g A I
    let evm1e := clipperCtorAfterStoppedState evm0e
    let evm1s := clipperCtorAfterStoppedState evm0s
    let evm2e := clipperCtorAfterSpotterState evm1e spotter
    let evm2s := clipperCtorAfterSpotterState evm1s spotter
    let evm3e := clipperCtorAfterDogState evm2e dog
    let evm3s := clipperCtorAfterDogState evm2s dog
    let evm4e := clipperCtorAfterBufState evm3e
    let evm4s := clipperCtorAfterBufState evm3s
    let evm5e := clipperCtorAfterWardsState evm4e
    let evm5s := clipperCtorAfterWardsState evm4s
    EVMStateEquiv evm5e evm5s := by
  intro evm0e evm0s evm1e evm1s evm2e evm2s evm3e evm3s evm4e evm4s evm5e evm5s
  have h0 : EVMStateEquiv evm0e evm0s := by
    simpa [evm0e, evm0s] using EVMStateEquiv.initState (g := g) rfl
  have h1 : EVMStateEquiv evm1e evm1s := by
    simpa [evm1e, evm1s, clipperCtorAfterStoppedState] using
      h0.storageStore_codeOwner ⟨14⟩ (show (⟨0⟩ : UInt256) = ⟨0⟩ by rfl)
  have hSpotter :
      setAddressOffset0Word
          (Solm.EVM.storageLoad evm1e evm1e.executionEnv.codeOwner ⟨3⟩)
          (EVM.word spotter.val) =
        setAddressOffset0Word
          (Solm.EVM.storageLoad evm1s evm1s.executionEnv.codeOwner ⟨3⟩)
          (EVM.word spotter.val) :=
    congrArg (fun old => setAddressOffset0Word old (EVM.word spotter.val))
      (h1.storageLoad_codeOwner ⟨3⟩)
  have h2 : EVMStateEquiv evm2e evm2s := by
    simpa [evm2e, evm2s, clipperCtorAfterSpotterState] using
      h1.storageStore_codeOwner ⟨3⟩ hSpotter
  have hDog :
      setAddressOffset0Word
          (Solm.EVM.storageLoad evm2e evm2e.executionEnv.codeOwner ⟨1⟩)
          (EVM.word dog.val) =
        setAddressOffset0Word
          (Solm.EVM.storageLoad evm2s evm2s.executionEnv.codeOwner ⟨1⟩)
          (EVM.word dog.val) :=
    congrArg (fun old => setAddressOffset0Word old (EVM.word dog.val))
      (h2.storageLoad_codeOwner ⟨1⟩)
  have h3 : EVMStateEquiv evm3e evm3s := by
    simpa [evm3e, evm3s, clipperCtorAfterDogState] using
      h2.storageStore_codeOwner ⟨1⟩ hDog
  have h4 : EVMStateEquiv evm4e evm4s := by
    simpa [evm4e, evm4s, clipperCtorAfterBufState] using
      h3.storageStore_codeOwner ⟨5⟩
        (show clipperCtorRayWord = clipperCtorRayWord by rfl)
  have hslotE :
      wardsSlot (.address evm4e.executionEnv.source) = clipperCtorCallerWardsSlot I := by
    simpa [evm4e, evm3e, evm2e, evm1e, evm0e, clipperCtorAfterBufState,
      clipperCtorAfterDogState, clipperCtorAfterSpotterState,
      clipperCtorAfterStoppedState, initState, storageStore_executionEnv] using
      clipperCtorCallerWardsSlot_eq I
  have hslotS :
      wardsSlot (.address evm4s.executionEnv.source) = clipperCtorCallerWardsSlot I := by
    simpa [evm4s, evm3s, evm2s, evm1s, evm0s, clipperCtorAfterBufState,
      clipperCtorAfterDogState, clipperCtorAfterSpotterState,
      clipperCtorAfterStoppedState, initState, storageStore_executionEnv] using
      clipperCtorCallerWardsSlot_eq I
  simpa [evm5e, evm5s, clipperCtorAfterWardsState, hslotE, hslotS] using
    h4.storageStore_codeOwner (clipperCtorCallerWardsSlot I)
      (show (⟨1⟩ : UInt256) = ⟨1⟩ by rfl)

set_option maxHeartbeats 3000000 in
/-- Every patch site is a declared immutable. -/
theorem immutableLayout_keys :
    ∀ site ∈ immutableLayout.sites, site.2.2 ∈ contract.immutables.map (·.name) := by
  decide

/-- The runtime deployed for immutables holding `vat` and a 32-byte `ilk` is the constructor's
    patched template. -/
theorem clipperDeployed_eq {imms : Store} {vat : AccountAddress} {ilk : List UInt8}
    (hvat : imms.get? "vat" = some (.address vat))
    (hilkv : imms.get? "ilk" = some (.fixedBytes bytes32Width ilk)) (hilk : ilk.length = 32) :
    immutableLayout.deployed clipperBytecode imms = clipperCtorPatchedRuntime vat ilk := by
  have hvatw : wordsOf imms "vat" = EVM.word vat.val := wordsOf_of_get hvat rfl
  have hilkw : wordsOf imms "ilk" = ABI.bytesToWord ilk :=
    wordsOf_of_get hilkv (by
      simp [valueToWord, bytes32Width, hilk, ABI.bytesToWord, fromByteArrayBigEndian,
        byteArray_toList_eq]
      rfl)
  simp only [Layout.deployed, Reasoning.Immutables.Layout.runtime,
    Reasoning.Immutables.Layout.writes, immutableLayout, offsets, List.flatMap_cons,
    List.flatMap_nil, List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.append_nil, hvatw, hilkw, clipperCtorPatchedRuntime, clipperCtorRuntimeWrites]

theorem clipperCtorFinalImms_get_vat (vat : AccountAddress) (ilk : List UInt8) :
    (clipperCtorFinalImms vat ilk).get? "vat" = some (.address vat) := by
  simp only [clipperCtorFinalImms, initialImmutables, contract, List.foldl]; grind

theorem clipperCtorFinalImms_get_ilk (vat : AccountAddress) (ilk : List UInt8) :
    (clipperCtorFinalImms vat ilk).get? "ilk" = some (.fixedBytes bytes32Width ilk) := by
  simp [clipperCtorFinalImms]

theorem clipperCtorFinalImms_fit (vat : AccountAddress) (ilk : List UInt8)
    (hilk : ilk.length = 32) : immutablesFit contract (clipperCtorFinalImms vat ilk) := by
  intro d hd
  simp only [contract, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl
  · exact ⟨_, clipperCtorFinalImms_get_vat vat ilk, rfl⟩
  · exact ⟨_, clipperCtorFinalImms_get_ilk vat ilk, by simp [elemValueFits, bytes32Width, hilk]⟩

theorem clipperConstructorCorrect :
    typedConstructorRefinement config clipperCreationBytecode contract
      (immutableLayout.deployed clipperBytecode) := by
  intro σ σ₀ g A I args deployedInitcode hdeploy hcode _hcalldata hperm
  rcases clipperCtorDeployment_shape hdeploy with
    ⟨vat, spotter, dog, ilk, hilk, hargs, hdeployed⟩
  subst args
  have hcodeCtor : I.code = clipperCtorCode vat spotter dog ilk := by
    rw [hcode, hdeployed]
  by_cases hwv : I.weiValue = ⟨0⟩
  · have hrd := clipperInitcodeSuccess
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      vat spotter dog ilk hilk hcodeCtor hperm hwv
    rcases RDretXiResultAccountMap (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (code := clipperCtorCode vat spotter dog ilk)
      (o := clipperCtorPatchedRuntime vat ilk) hcodeCtor hrd with hOOG | ⟨g', A', hsuccess⟩
    · exact .outOfGas
        (by simpa [Sat256.ofUInt256] using hOOG)
    · let evm0 := initState σ σ₀ (Sat256.ofUInt256 g) A I
      let evm1 := clipperCtorAfterStoppedState evm0
      let evm2 := clipperCtorAfterSpotterState evm1 spotter
      let evm3 := clipperCtorAfterDogState evm2 dog
      let evm4 := clipperCtorAfterBufState evm3
      let evm5 := clipperCtorAfterWardsState evm4
      have hstate : EVMStateEquiv evm5 evm5 := by
        simpa [evm0, evm1, evm2, evm3, evm4, evm5] using
          clipperCtorStateEquiv (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
            (g := Sat256.ofUInt256 g) spotter dog
      let σFinal := sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner
              (sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩)
              ⟨3⟩
              (setAddressOffset0Word
                (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩) I ⟨3⟩)
                (EVM.word spotter.val)))
            ⟨1⟩
            (setAddressOffset0Word
              (solcSlotWord
                (sstoreAccountMap I.codeOwner
                  (sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩) ⟨3⟩
                  (setAddressOffset0Word
                    (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨14⟩ ⟨0⟩) I ⟨3⟩)
                    (EVM.word spotter.val))) I ⟨1⟩)
              (EVM.word dog.val)))
          ⟨5⟩ clipperCtorRayWord)
        (clipperCtorCallerWardsSlot I) ⟨1⟩
      have hMapFinal : σFinal = evm5.accountMap := by
        simpa [σFinal, evm0, evm1, evm2, evm3, evm4, evm5,
          clipperCtorAfterWardsState, clipperCtorAfterBufState,
          clipperCtorAfterDogState, clipperCtorAfterSpotterState,
          clipperCtorAfterStoppedState, initState, storageStore_accountMap,
          storageStore_executionEnv, Solm.EVM.storageLoad, State.lookupAccount,
          Account.lookupStorage, solcSlotWord, clipperCtorCallerWardsSlot_eq] using
          hstate.accountMap
      refine .execution
        (by simpa [Sat256.ofUInt256, σFinal] using hsuccess)
        (by
          simpa [evm0, evm1, evm2, evm3, evm4, evm5] using
            clipperSolmCtorExecSuccess
              (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
              vat spotter dog ilk hilk hwv)
        ?_ ?_
      · refine ctorResultEquiv.success rfl rfl hMapFinal ?_
        exact (clipperDeployed_eq (clipperCtorFinalImms_get_vat vat ilk)
          (clipperCtorFinalImms_get_ilk vat ilk) hilk).symm
      · exact clipperCtorFinalImms_fit vat ilk hilk
  · have hrd := clipperInitcodeNonpayableRevert
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := Sat256.ofUInt256 g)
      vat spotter dog ilk hcodeCtor hperm hwv
    rcases RDrev.xiResult (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) (code := clipperCtorCode vat spotter dog ilk)
      hcodeCtor hrd with hOOG | ⟨g', out, hrev⟩
    · exact .outOfGas
        (by simpa [Sat256.ofUInt256] using hOOG)
    · exact .execution
        (by simpa [Sat256.ofUInt256] using hrev)
        (clipperSolmCtorExecReverts_nonpayable
          (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          vat spotter dog ilk hwv)
        (ctorResultEquiv.revert rfl rfl) trivial

end Benchmarks.Dss.Clipper
