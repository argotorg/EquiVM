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

abbrev clipperCtorVatLocals (vat spotter dog : AccountAddress) (ilk : List UInt8) : Store :=
  (clipperCtorLocals vat spotter dog ilk).insert "imm_vat" (.address vat)

abbrev clipperCtorFinalLocals (vat spotter dog : AccountAddress) (ilk : List UInt8) : Store :=
  (clipperCtorVatLocals vat spotter dog ilk).insert "imm_ilk"
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

theorem evalExpr_clipperCtorLocalVat {v : ClipperImmutables} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? (config v) { contract := contract v, locals := clipperCtorLocals vat spotter dog ilk }
      evm (.var "vat_") =
      .ok (.address vat) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_clipperCtorLocalSpotter {v : ClipperImmutables} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? (config v) { contract := contract v, locals := clipperCtorLocals vat spotter dog ilk }
      evm (.var "spotter_") =
      .ok (.address spotter) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_clipperCtorLocalDog {v : ClipperImmutables} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? (config v) { contract := contract v, locals := clipperCtorLocals vat spotter dog ilk }
      evm (.var "dog_") =
      .ok (.address dog) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorLocals, store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_clipperCtorLocalIlk {v : ClipperImmutables} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? (config v) { contract := contract v, locals := clipperCtorLocals vat spotter dog ilk }
      evm (.var "ilk_") =
      .ok (.fixedBytes bytes32Width ilk) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorLocals, store_get_self]

theorem evalExpr_clipperCtorVatLocalIlk {v : ClipperImmutables} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? (config v) { contract := contract v, locals := clipperCtorVatLocals vat spotter dog ilk }
      evm (.var "ilk_") =
      .ok (.fixedBytes bytes32Width ilk) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorVatLocals, store_get_ne _ _ (by decide),
    clipperCtorLocals, store_get_self]

theorem evalExpr_clipperCtorFinalLocalSpotter {v : ClipperImmutables} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? (config v) { contract := contract v, locals := clipperCtorFinalLocals vat spotter dog ilk }
      evm (.var "spotter_") =
      .ok (.address spotter) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorFinalLocals, store_get_ne _ _ (by decide),
    clipperCtorVatLocals, store_get_ne _ _ (by decide),
    clipperCtorLocals, store_get_ne _ _ (by decide),
    store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_clipperCtorFinalLocalDog {v : ClipperImmutables} {evm : EVM.State}
    (vat spotter dog : AccountAddress) (ilk : List UInt8) :
    evalExpr? (config v) { contract := contract v, locals := clipperCtorFinalLocals vat spotter dog ilk }
      evm (.var "dog_") =
      .ok (.address dog) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [clipperCtorFinalLocals, store_get_ne _ _ (by decide),
    clipperCtorVatLocals, store_get_ne _ _ (by decide),
    clipperCtorLocals, store_get_ne _ _ (by decide), store_get_self]

private theorem assign_clipperCtorUint256Storage {v : ClipperImmutables}
    (evm : EVM.State) (locals : Store) (ref : StorageRef) (er : EvaledStorageRef)
    (slot value : UInt256) (hbase : locals.get? ref.base = none)
    (her : evalStorageRef (config v) { contract := contract v, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? (contract v).storage er = some uint256St)
    (hloc : (config v).storage.layout er = fun _ => some (wordLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot value
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage ref (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar (ty := uint256St) (er := er) (loc := wordLoc slot)
    (hbase := hbase) (her := her) (hty := hty) (hloc := hloc)
  simpa [evm'] using storageLocStore_uint256 evm slot value

private theorem assign_clipperCtorAddressStorage {v : ClipperImmutables}
    (evm : EVM.State) (locals : Store) (ref : StorageRef) (er : EvaledStorageRef)
    (slot : UInt256) (addrValue : AccountAddress) (hbase : locals.get? ref.base = none)
    (her : evalStorageRef (config v) { contract := contract v, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? (contract v).storage er = some addrSt)
    (hloc : (config v).storage.layout er = fun _ => some (addrLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (EVM.word addrValue.val))
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage ref (.address addrValue) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
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

theorem assign_clipperCtorStoppedStorage {v : ClipperImmutables}
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "stopped" = none) :
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage stoppedRef (.int 0) =
        .ok ({ contract := contract v, locals := locals }, clipperCtorAfterStoppedState evm) := by
  simpa [clipperCtorAfterStoppedState] using
    assign_clipperCtorUint256Storage evm locals stoppedRef { base := "stopped", steps := [] }
      ⟨14⟩ ⟨0⟩ (by simpa [stoppedRef] using hbase)
      (by simp [stoppedRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by funext evm; simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_clipperCtorSpotterStorage {v : ClipperImmutables}
    (evm : EVM.State) (locals : Store) (spotter : AccountAddress)
    (hbase : locals.get? "spotter" = none) :
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage spotterRef (.address spotter) =
        .ok ({ contract := contract v, locals := locals },
          clipperCtorAfterSpotterState evm spotter) := by
  exact assign_clipperCtorAddressStorage evm locals spotterRef
    { base := "spotter", steps := [] } ⟨3⟩ spotter
    (by simpa [spotterRef] using hbase)
    (by simp [spotterRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by funext evm; simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_clipperCtorDogStorage {v : ClipperImmutables}
    (evm : EVM.State) (locals : Store) (dog : AccountAddress)
    (hbase : locals.get? "dog" = none) :
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage dogRef (.address dog) =
        .ok ({ contract := contract v, locals := locals }, clipperCtorAfterDogState evm dog) := by
  exact assign_clipperCtorAddressStorage evm locals dogRef { base := "dog", steps := [] }
    ⟨1⟩ dog (by simpa [dogRef] using hbase)
    (by simp [dogRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by funext evm; simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_clipperCtorBufStorage {v : ClipperImmutables}
    (evm : EVM.State) (locals : Store) (hbase : locals.get? "buf" = none) :
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage bufRef (.int RAY) =
        .ok ({ contract := contract v, locals := locals }, clipperCtorAfterBufState evm) := by
  have hray : RAY = Int.ofNat clipperCtorRayWord.toNat := by native_decide
  rw [hray]
  simpa [clipperCtorAfterBufState] using
    assign_clipperCtorUint256Storage evm locals bufRef { base := "buf", steps := [] }
      ⟨5⟩ clipperCtorRayWord (by simpa [bufRef] using hbase)
      (by simp [bufRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by funext evm; simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_clipperCtorWardsCaller {v : ClipperImmutables}
    (evm : EVM.State) {locals : Store} (hbase : locals.get? "wards" = none) :
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract v, locals := locals }, clipperCtorAfterWardsState evm) := by
  have her : evalStorageRef (config v) { contract := contract v, locals := locals } evm
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

private theorem clipperCtor_storageStore_executionEnv (evm : EVM.State)
    (addr : AccountAddress) (slot value : UInt256) :
    (Solm.EVM.storageStore evm addr slot value).executionEnv = evm.executionEnv := by
  unfold Solm.EVM.storageStore
  cases State.lookupAccount evm addr <;> rfl

theorem clipperCtorFinalLocals_get_imm_vat (vat spotter dog : AccountAddress)
    (ilk : List UInt8) :
    (clipperCtorFinalLocals vat spotter dog ilk).get? "imm_vat" = some (.address vat) := by
  rw [clipperCtorFinalLocals, store_get_ne _ _ (by decide),
    clipperCtorVatLocals, store_get_self]

theorem clipperCtorFinalLocals_get_imm_ilk (vat spotter dog : AccountAddress)
    (ilk : List UInt8) :
    (clipperCtorFinalLocals vat spotter dog ilk).get? "imm_ilk" =
      some (.fixedBytes bytes32Width ilk) := by
  simp [clipperCtorFinalLocals]

theorem clipperCtorRuntimeCodeOf (vat spotter dog : AccountAddress)
    (ilk : List UInt8) (hilk : ilk.length = 32) :
    runtimeCodeOf clipperBytecode (clipperCtorFinalLocals vat spotter dog ilk) =
      patchRuntime clipperBytecode (patches (clipperCtorImmutables vat ilk hilk)) := by
  unfold runtimeCodeOf patches patchesFrom immValues
  simp only [offsets, List.foldrM_cons, List.foldrM_nil, pure, bind]
  rw [clipperCtorFinalLocals_get_imm_ilk, clipperCtorFinalLocals_get_imm_vat]
  simp [clipperCtorImmutables, List.lookup_cons, wordBytes?, valueToWord,
    bytes32Width, hilk]

theorem clipperCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (v : ClipperImmutables) (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := clipperCtorLocals vat spotter dog ilk
    let vatLocals := clipperCtorVatLocals vat spotter dog ilk
    let finalLocals := clipperCtorFinalLocals vat spotter dog ilk
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := clipperCtorAfterStoppedState evm0
    let evm2 := clipperCtorAfterSpotterState evm1 spotter
    let evm3 := clipperCtorAfterDogState evm2 dog
    let evm4 := clipperCtorAfterBufState evm3
    let evm5 := clipperCtorAfterWardsState evm4
    ExecBlock (config v) { contract := contract v, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract v, locals := finalLocals } evm5) := by
  intro locals vatLocals finalLocals evm0 evm1 evm2 evm3 evm4 evm5
  have hstopped := assign_clipperCtorStoppedStorage (v := v) evm0 locals
    (by simp [locals, clipperCtorLocals])
  have hspotter := assign_clipperCtorSpotterStorage (v := v) evm1 finalLocals spotter
    (by simp [finalLocals, clipperCtorFinalLocals, clipperCtorVatLocals, clipperCtorLocals])
  have hdog := assign_clipperCtorDogStorage (v := v) evm2 finalLocals dog
    (by simp [finalLocals, clipperCtorFinalLocals, clipperCtorVatLocals, clipperCtorLocals])
  have hbuf := assign_clipperCtorBufStorage (v := v) evm3 finalLocals
    (by simp [finalLocals, clipperCtorFinalLocals, clipperCtorVatLocals, clipperCtorLocals])
  have hwards := assign_clipperCtorWardsCaller (v := v) evm4 (locals := finalLocals)
    (by simp [finalLocals, clipperCtorFinalLocals, clipperCtorVatLocals, clipperCtorLocals])
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hstopped) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by
      change (clipperCtorAfterStoppedState evm0).executionEnv.weiValue = ⟨0⟩
      rw [clipperCtorAfterStoppedState, clipperCtor_storageStore_executionEnv]
      simpa [evm0, initState] using hwv)
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .address vat) ?_) ?_
  · simpa [locals] using evalExpr_clipperCtorLocalVat (v := v) (evm := evm1)
      vat spotter dog ilk
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .fixedBytes bytes32Width ilk) ?_) ?_
  · exact evalExpr_clipperCtorVatLocalIlk (v := v) (evm := evm1)
      vat spotter dog ilk
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hspotter) ?_
  · exact evalExpr_clipperCtorFinalLocalSpotter (v := v) (evm := evm1)
      vat spotter dog ilk
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hdog) ?_
  · exact evalExpr_clipperCtorFinalLocalDog (v := v) (evm := evm2)
      vat spotter dog ilk
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure, RAY]) hbuf) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hwards)
    ExecBlock.nil

theorem clipperSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (v : ClipperImmutables) (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec (config v) (contract v)
      [.address vat, .address spotter, .address dog, .fixedBytes bytes32Width ilk]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := contract v, locals :=
          clipperCtorFinalLocals vat spotter dog ilk }
        (clipperCtorAfterWardsState
          (clipperCtorAfterBufState
            (clipperCtorAfterDogState
              (clipperCtorAfterSpotterState
                (clipperCtorAfterStoppedState
                  (initState createdAccounts genesisBlockHeader blocks σ σ₀
                    (Sat256.ofUInt256 g) A I)) spotter) dog))) none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := clipperCtorLocals vat spotter dog ilk) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK (clipperCtorBodySuccess
        (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
        (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        v vat spotter dog ilk hwv)

theorem clipperSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv} {g : UInt256}
    (v : ClipperImmutables) (vat spotter dog : AccountAddress) (ilk : List UInt8)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec (config v) (contract v)
      [.address vat, .address spotter, .address dog, .fixedBytes bytes32Width ilk]
      createdAccounts genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
    (Sat256.ofUInt256 g) A I
  let evm1 := clipperCtorAfterStoppedState evm0
  have hstopped := assign_clipperCtorStoppedStorage (v := v) evm0
    (clipperCtorLocals vat spotter dog ilk)
    (by simp [clipperCtorLocals])
  have hbody : ExecBlock (config v)
      { contract := contract v, locals := clipperCtorLocals vat spotter dog ilk } evm0
      constructorDecl.body .reverted := by
    simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
    refine ExecBlock.consNormal
      (ExecStmt.assign (by simp [evalExpr?, pure]) hstopped) ?_
    exact blockReverts_nonPayable (by
      change (clipperCtorAfterStoppedState evm0).executionEnv.weiValue ≠ ⟨0⟩
      rw [clipperCtorAfterStoppedState, clipperCtor_storageStore_executionEnv]
      simpa [evm0, initState] using hwv)
  refine solmCtorExec.intro (evmState := evm0)
    (argsStore := clipperCtorLocals vat spotter dog ilk) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockRevert hbody

end Benchmarks.Dss.Clipper
