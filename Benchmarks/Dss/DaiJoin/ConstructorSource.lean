import Benchmarks.Dss.DaiJoin.Common
import Reasoning.Initcode
import Reasoning.ExternalCall
import Solm.Equiv

/-!
# MakerDAO/Sky DSS DaiJoin constructor Solm source semantics
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.DaiJoin

set_option maxRecDepth 2000000

abbrev daiJoinCtorArgsTail (vat dai : AccountAddress) : ByteArray :=
  (EVM.Word.toBytesBE (EVM.word vat.val)).toByteArray ++
    (EVM.Word.toBytesBE (EVM.word dai.val)).toByteArray

noncomputable def daiJoinCtorCode (vat dai : AccountAddress) : ByteArray :=
  daiJoinCreationBytecode ++ daiJoinCtorArgsTail vat dai

theorem daiJoinCtorDeployment_shape {args : List Value} {deployedInitcode : ByteArray}
    (hdeploy : config.selfDeployment daiJoinCreationBytecode args = some deployedInitcode) :
    ∃ vat dai : AccountAddress,
      args = [.address vat, .address dai] ∧ deployedInitcode = daiJoinCtorCode vat dai := by
  simp [config, contract, constructorDecl, Solm.genSolidityConstructorDeployment] at hdeploy
  cases args with
  | nil =>
      simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr] at hdeploy
  | cons a rest =>
      cases rest with
      | nil =>
          cases a <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
            ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
            ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
      | cons b rest2 =>
          cases rest2 with
          | cons _ _ =>
              cases a <;> cases b <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
                ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
          | nil =>
              cases a <;> cases b <;> simp [ABI.encodeABIValues?, ABI.encodeABIValuesFrom?, addr,
                ABI.abiTupleHeadSize?, ABI.staticABIEncodedSize?, ABI.isDynamicABIType,
                ABI.encodeABIValue?, ABI.encodeABIWord?] at hdeploy
              rename_i vat dai
              refine ⟨vat, dai, rfl, ?_⟩
              simpa [daiJoinCtorCode, daiJoinCtorArgsTail] using hdeploy.symm

abbrev daiJoinCtorLocals (vat dai : AccountAddress) : Store :=
  ((∅ : Store).insert "vat_" (.address vat)).insert "dai_" (.address dai)

abbrev daiJoinCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev daiJoinCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ ⟨1⟩

abbrev daiJoinCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨1⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
      (EVM.word vat.val))

abbrev daiJoinCtorAfterDaiState (evm : EVM.State) (dai : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (EVM.word dai.val))

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

theorem daiJoin_word_val_addr_canonical (a : AccountAddress) :
    (EVM.word a.val).toNat < EVM.addressModulus := by
  have hsize : AccountAddress.size < UInt256.size := by decide
  have hval : (EVM.word a.val).toNat = a.val := by
    change (UInt256.ofNat a.val).toNat = a.val
    rw [UInt256.toNat_ofNat_of_lt (lt_trans a.isLt hsize)]
  rw [hval]
  exact a.isLt

theorem evalExpr_daiJoinCtorLocalVat {evm : EVM.State} (vat dai : AccountAddress) :
    evalExpr? config { contract := contract, locals := daiJoinCtorLocals vat dai } evm
      (.var "vat_") = .ok (.address vat) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [daiJoinCtorLocals, store_get_ne _ _ (by decide +native), store_get_self]

theorem evalExpr_daiJoinCtorLocalDai {evm : EVM.State} (vat dai : AccountAddress) :
    evalExpr? config { contract := contract, locals := daiJoinCtorLocals vat dai } evm
      (.var "dai_") = .ok (.address dai) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [daiJoinCtorLocals, store_get_self]

theorem assign_daiJoinCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := daiJoinCtorAfterWardsState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals } evm
        (wardsRef sender) =
          .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some evm' := by
    simpa [evm', daiJoinCtorAfterWardsState] using
      daiJoinStorageLocStore_uint256 evm (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := uint256St) (loc := wordLoc (wardsSlot (.address evm.executionEnv.source)))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

private theorem assign_daiJoinCtorAddressStorage (evm : EVM.State) (locals : Store)
    (ref : StorageRef) (er : EvaledStorageRef) (slot : UInt256) (addrValue : AccountAddress)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some (.elem .address))
    (hloc : config.storage.layout er = fun _ => some (addrLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot
      (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
        (EVM.word addrValue.val))
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ref (.address addrValue) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  have hvalue :
      (.address addrValue : Value) =
        .address (AccountAddress.ofNat (EVM.word addrValue.val).toNat) := by
    rw [accountAddress_of_word_val]
  rw [hvalue]
  have hstore :
      storageLocStore evm (addrLoc slot)
          (.address (AccountAddress.ofNat (EVM.word addrValue.val).toNat)) =
        some evm' := by
    simpa [addrLoc, evm'] using
      storageLocStore_address_offset0 evm slot (EVM.word addrValue.val)
        (daiJoin_word_val_addr_canonical addrValue)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc slot)
    (hbase := hbase)
    (her := her)
    (hty := hty)
    (hloc := hloc)
    (hscalar := by trivial)
    (hstore := hstore)

private theorem assign_daiJoinCtorUint256Storage (evm : EVM.State) (locals : Store)
    (ref : StorageRef) (er : EvaledStorageRef) (slot value : UInt256)
    (hbase : locals.get? ref.base = none)
    (her : evalStorageRef config { contract := contract, locals := locals } evm ref = .ok er)
    (hty : storageTypeAt? contract.storage er = some uint256St)
    (hloc : config.storage.layout er = fun _ => some (wordLoc slot)) :
    let evm' := Solm.EVM.storageStore evm evm.executionEnv.codeOwner slot value
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ref (.int (Int.ofNat value.toNat)) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint256St)
      (er := er)
      (loc := wordLoc slot)
      (hbase := hbase)
      (her := her)
      (hty := hty)
      (hloc := hloc)
  simpa [evm'] using daiJoinStorageLocStore_uint256 evm slot value

theorem assign_daiJoinCtorLiveStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "live" = none) :
    let evm' := daiJoinCtorAfterLiveState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [daiJoinCtorAfterLiveState] using
    assign_daiJoinCtorUint256Storage evm locals liveRef { base := "live", steps := [] } ⟨3⟩
      ⟨1⟩
      (by simpa [liveRef] using hbase)
      (by simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_daiJoinCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := daiJoinCtorAfterVatState evm vat
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_daiJoinCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨1⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_daiJoinCtorDaiStorage (evm : EVM.State) (locals : Store)
    (dai : AccountAddress) (hbase : locals.get? "dai" = none) :
    let evm' := daiJoinCtorAfterDaiState evm dai
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage daiRef (.address dai) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_daiJoinCtorAddressStorage evm locals daiRef { base := "dai", steps := [] } ⟨2⟩ dai
    (by simpa [daiRef] using hbase)
    (by simp [daiRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem daiJoinCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = mapSlot (UInt256.ofNat I.source.val) ⟨0⟩ := by
  unfold wardsSlot mapSlot
  rw [keyValueToWord_address]

theorem daiJoinCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat dai : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := daiJoinCtorLocals vat dai
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := daiJoinCtorAfterWardsState evm0
    let evm2 := daiJoinCtorAfterLiveState evm1
    let evm3 := daiJoinCtorAfterVatState evm2 vat
    let evm4 := daiJoinCtorAfterDaiState evm3 dai
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals } evm4) := by
  intro locals evm0 evm1 evm2 evm3 evm4
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, daiJoinCtorAfterWardsState] using
      assign_daiJoinCtorWardsCaller evm0 (locals := locals) (by simp [locals, daiJoinCtorLocals])
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, daiJoinCtorAfterLiveState] using
      assign_daiJoinCtorLiveStorage evm1 locals (by simp [locals, daiJoinCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm2
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3, daiJoinCtorAfterVatState] using
      assign_daiJoinCtorVatStorage evm2 locals vat (by simp [locals, daiJoinCtorLocals])
  have hassignDai :
      assignStorageRef? config { contract := contract, locals := locals } evm3
        .storage daiRef (.address dai) =
          .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4, daiJoinCtorAfterDaiState] using
      assign_daiJoinCtorDaiStorage evm3 locals dai (by simp [locals, daiJoinCtorLocals])
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by rw [evalExpr?]; rfl) hassignLive) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_daiJoinCtorLocalVat (evm := evm2) vat dai
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignDai) ExecBlock.nil
  · simpa [locals] using evalExpr_daiJoinCtorLocalDai (evm := evm3) vat dai

theorem daiJoinSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat dai : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address vat, .address dai] createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I
      (.returned { contract := contract, locals := daiJoinCtorLocals vat dai }
        (daiJoinCtorAfterDaiState
          (daiJoinCtorAfterVatState
            (daiJoinCtorAfterLiveState
              (daiJoinCtorAfterWardsState
                (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)))
            vat)
          dai)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := daiJoinCtorLocals vat dai)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (daiJoinCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) vat dai hwv)

theorem daiJoinSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat dai : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address vat, .address dai] createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := daiJoinCtorLocals vat dai)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := daiJoinCtorLocals vat dai) hwv

end Benchmarks.Dss.DaiJoin
