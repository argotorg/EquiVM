import Benchmarks.Dss.Clipper.ConstructorBase
import Reasoning.ExternalCall

/-!
# MakerDAO/Sky DSS Clipper constructor source semantics
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Clipper.Immutables

namespace Benchmarks.Dss.Clipper

set_option maxRecDepth 2000000
set_option maxHeartbeats 2000000

abbrev clipperCtorLocals (vat spotter dog : AccountAddress) (ilk : List UInt8) : Store :=
  ((((∅ : Store).insert "vat_" (.address vat)).insert "spotter_" (.address spotter)).insert
    "dog_" (.address dog)).insert "ilk_" (.fixedBytes bytes32Width ilk)

/-- The constructor's final immutables: `vat` then `ilk` set to the arguments. -/
abbrev clipperCtorFinalImms (vat : AccountAddress) (ilk : List UInt8) : Store :=
  ((initialImmutables contract).insert "vat" (.address vat)).insert "ilk"
    (.fixedBytes bytes32Width ilk)

abbrev clipperCtorAfterStoppedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨14⟩ ⟨0⟩

abbrev clipperCtorAfterSpotterState (evm : EVM.State) (spotter : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      (EVM.word spotter.val))

abbrev clipperCtorAfterDogState (evm : EVM.State) (dog : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      (EVM.word dog.val))

abbrev clipperCtorAfterBufState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ clipperCtorRayWord

abbrev clipperCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

theorem evalExpr_clipperCtorLocalVat {imms : Store} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? config { contract := contract, locals := clipperCtorLocals vat spotter dog ilk, immutables := imms }
      evm (.var "vat_") =
      .ok (.address vat) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_clipperCtorLocalSpotter {imms : Store} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? config { contract := contract, locals := clipperCtorLocals vat spotter dog ilk, immutables := imms }
      evm (.var "spotter_") =
      .ok (.address spotter) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_clipperCtorLocalDog {imms : Store} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? config { contract := contract, locals := clipperCtorLocals vat spotter dog ilk, immutables := imms }
      evm (.var "dog_") =
      .ok (.address dog) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorLocals, store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_clipperCtorLocalIlk {imms : Store} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? config { contract := contract, locals := clipperCtorLocals vat spotter dog ilk, immutables := imms }
      evm (.var "ilk_") =
      .ok (.fixedBytes bytes32Width ilk) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorLocals, store_get_self]

private theorem assign_clipperCtorUint256Storage {imms : Store}
    (evm : EVM.State) (locals : Store) (ref : StorageRef) (er : EvaledStorageRef)
    (slot value : UInt256) (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals, immutables := imms } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some uint256St)
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot value
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage ref (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals, immutables := imms }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar (ty := uint256St) (er := er) (loc := wordLoc slot)
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)
  simpa [evm'] using storageLocStore_uint256 evm slot value

private theorem assign_clipperCtorAddressStorage {imms : Store}
    (evm : EVM.State) (locals : Store) (ref : StorageRef) (er : EvaledStorageRef)
    (slot : UInt256) (addrValue : AccountAddress) (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals, immutables := imms } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some addrSt)
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (EVM.word addrValue.val))
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage ref (.address addrValue) =
        .ok ({ contract := contract, locals := locals, immutables := imms }, evm') := by
  intro evm'
  have hvalue : (.address addrValue : Value) =
      .address (AccountAddress.ofNat (EVM.word addrValue.val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  have hstore :
      storageLocStore evm (addrLoc slot)
          (.address (AccountAddress.ofNat (EVM.word addrValue.val).toNat)) = some evm' := by
    simpa [addrLoc, evm'] using storageLocStore_address_offset0 evm slot
      (EVM.word addrValue.val) (clipperCtorAddressWord_canonical addrValue)
  exact assignStorageRef_storage_scalar_value
    (ty := addrSt) (loc := addrLoc slot) (hbase := hbase) (her := her) (hty := hty)
    (hloc := hloc) (hscalar := by trivial) (hstore := hstore)

theorem assign_clipperCtorStoppedStorage {imms : Store}
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "stopped" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage stoppedRef (.int 0) =
        .ok ({ contract := contract, locals := locals, immutables := imms }, clipperCtorAfterStoppedState evm) := by
  simpa [clipperCtorAfterStoppedState] using
    assign_clipperCtorUint256Storage evm locals stoppedRef { base := "stopped", steps := [] }
      ⟨14⟩ ⟨0⟩ (by simpa [stoppedRef] using hbase)
      (by simp [stoppedRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by funext evm; simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_clipperCtorSpotterStorage {imms : Store}
    (evm : EVM.State) (locals : Store) (spotter : AccountAddress)
    (hbase : locals.get? "spotter" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage spotterRef (.address spotter) =
        .ok ({ contract := contract, locals := locals, immutables := imms },
          clipperCtorAfterSpotterState evm spotter) := by
  exact assign_clipperCtorAddressStorage evm locals spotterRef
    { base := "spotter", steps := [] } ⟨3⟩ spotter
    (by simpa [spotterRef] using hbase)
    (by simp [spotterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by funext evm; simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_clipperCtorDogStorage {imms : Store}
    (evm : EVM.State) (locals : Store) (dog : AccountAddress)
    (hbase : locals.get? "dog" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage dogRef (.address dog) =
        .ok ({ contract := contract, locals := locals, immutables := imms }, clipperCtorAfterDogState evm dog) := by
  exact assign_clipperCtorAddressStorage evm locals dogRef { base := "dog", steps := [] }
    ⟨1⟩ dog (by simpa [dogRef] using hbase)
    (by simp [dogRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by funext evm; simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_clipperCtorBufStorage {imms : Store}
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "buf" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage bufRef (.int RAY) =
        .ok ({ contract := contract, locals := locals, immutables := imms }, clipperCtorAfterBufState evm) := by
  have hray : RAY = Int.ofNat clipperCtorRayWord.toNat := by native_decide
  rw [hray]
  simpa [clipperCtorAfterBufState] using
    assign_clipperCtorUint256Storage evm locals bufRef { base := "buf", steps := [] }
      ⟨5⟩ clipperCtorRayWord (by simpa [bufRef] using hbase)
      (by simp [bufRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by funext evm; simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_clipperCtorWardsCaller {imms : Store}
    (evm : EVM.State) {locals : Store} (hbase : locals.get? "wards" = none) :
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals, immutables := imms }, clipperCtorAfterWardsState evm) := by
  have her : evalStorageRef config { contract := contract, locals := locals, immutables := imms } evm
      (wardsRef sender) =
        .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore : storageLocStore evm
      (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some (clipperCtorAfterWardsState evm) := by
    simpa [clipperCtorAfterWardsState] using storageLocStore_uint256 evm
      (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := uint256St) (loc := wordLoc (wardsSlot (.address evm.executionEnv.source)))
    (hbase := by simpa [wardsRef] using hbase) (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem clipperCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = clipperCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot clipperCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

private theorem clipperCtor_storageStore_executionEnv (evm : EVM.State)
    (addr : AccountAddress) (slot value : UInt256) :
    (Solm.EVM.storageStore evm addr slot value).executionEnv = evm.executionEnv := by
  unfold Solm.EVM.storageStore
  cases State.lookupAccount evm addr <;> rfl

theorem clipperCtorBodySuccess
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := clipperCtorLocals vat spotter dog ilk
    let evm0 := initState σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := clipperCtorAfterStoppedState evm0
    let evm2 := clipperCtorAfterSpotterState evm1 spotter
    let evm3 := clipperCtorAfterDogState evm2 dog
    let evm4 := clipperCtorAfterBufState evm3
    let evm5 := clipperCtorAfterWardsState evm4
    ExecBlock config
      { contract := contract, locals := locals, immutables := initialImmutables contract }
      evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals, immutables := clipperCtorFinalImms vat ilk }
        evm5) := by
  intro locals evm0 evm1 evm2 evm3 evm4 evm5
  have hbase : ∀ n, n ∉ ["vat_", "spotter_", "dog_", "ilk_"] → locals.get? n = none := by
    intro n hn
    simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hn
    simp [locals, clipperCtorLocals, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2,
      Ne.symm hn.1, Ne.symm hn.2.1, Ne.symm hn.2.2.1, Ne.symm hn.2.2.2]
  have hstopped := assign_clipperCtorStoppedStorage (imms := initialImmutables contract) evm0
    locals (hbase "stopped" (by decide))
  have hspotter := assign_clipperCtorSpotterStorage (imms := clipperCtorFinalImms vat ilk) evm1
    locals spotter (hbase "spotter" (by decide))
  have hdog := assign_clipperCtorDogStorage (imms := clipperCtorFinalImms vat ilk) evm2 locals dog
    (hbase "dog" (by decide))
  have hbuf := assign_clipperCtorBufStorage (imms := clipperCtorFinalImms vat ilk) evm3 locals
    (hbase "buf" (by decide))
  have hwards := assign_clipperCtorWardsCaller (imms := clipperCtorFinalImms vat ilk) evm4
    (locals := locals) (hbase "wards" (by decide))
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hstopped) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by
      rw [clipperCtorAfterStoppedState, clipperCtor_storageStore_executionEnv]
      simpa [evm0, initState] using hwv)
  refine ExecBlock.consNormal
    (ExecStmt.setImmutable (value := .address vat) (ty := .address) ?_ rfl rfl) ?_
  · exact evalExpr_clipperCtorLocalVat (evm := evm1) vat spotter dog ilk
  refine ExecBlock.consNormal
    (ExecStmt.setImmutable (value := .fixedBytes bytes32Width ilk)
      (ty := .bytes ⟨31, by decide⟩) ?_ rfl ?_) ?_
  · exact evalExpr_clipperCtorLocalIlk (evm := evm1) vat spotter dog ilk
  · simp [elemValueFits, bytes32Width, hilk]
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hspotter) ?_
  · exact evalExpr_clipperCtorLocalSpotter (evm := evm1) vat spotter dog ilk
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hdog) ?_
  · exact evalExpr_clipperCtorLocalDog (evm := evm2) vat spotter dog ilk
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure, RAY]) hbuf) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hwards)
    ExecBlock.nil

theorem clipperSolmCtorExecSuccess
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) (hilk : ilk.length = 32)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract
      [.address vat, .address spotter, .address dog, .fixedBytes bytes32Width ilk]
      σ σ₀ g A I
      (.returned
        { contract := contract, locals := clipperCtorLocals vat spotter dog ilk,
          immutables := clipperCtorFinalImms vat ilk }
        (clipperCtorAfterWardsState
          (clipperCtorAfterBufState
            (clipperCtorAfterDogState
              (clipperCtorAfterSpotterState
                (clipperCtorAfterStoppedState
                  (initState σ σ₀
                    (Sat256.ofUInt256 g) A I)) spotter) dog))) none) := by
  refine solmCtorExec.intro
    (evmState := initState σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := clipperCtorLocals vat spotter dog ilk) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · exact ExecFuncBody.execBlockOK (clipperCtorBodySuccess
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) vat spotter dog ilk hilk hwv)

theorem clipperSolmCtorExecReverts_nonpayable
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract
      [.address vat, .address spotter, .address dog, .fixedBytes bytes32Width ilk]
      σ σ₀ g A I .reverted := by
  let evm0 := initState σ σ₀
    (Sat256.ofUInt256 g) A I
  have hstopped := assign_clipperCtorStoppedStorage (imms := initialImmutables contract) evm0
    (clipperCtorLocals vat spotter dog ilk)
    (by simp [clipperCtorLocals])
  have hbody : ExecBlock config
      { contract := contract, locals := clipperCtorLocals vat spotter dog ilk,
        immutables := initialImmutables contract } evm0
      constructorDecl.body .reverted := by
    simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) hstopped) ?_
    exact blockReverts_nonPayable (by
      rw [clipperCtorAfterStoppedState, clipperCtor_storageStore_executionEnv]
      simpa [evm0, initState] using hwv)
  refine solmCtorExec.intro (evmState := evm0)
    (argsStore := clipperCtorLocals vat spotter dog ilk) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · exact ExecFuncBody.execBlockRevert hbody

end Benchmarks.Dss.Clipper
