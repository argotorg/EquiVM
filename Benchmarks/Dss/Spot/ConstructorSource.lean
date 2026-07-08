import Benchmarks.Dss.Spot.ConstructorBase

/-!
# MakerDAO/Sky DSS Spotter constructor Solm source semantics
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Spot

set_option maxRecDepth 2000000

abbrev spotCtorLocals (vat : AccountAddress) : Store :=
  (∅ : Store).insert "vat_" (.address vat)

abbrev spotCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev spotCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (EVM.word vat.val))

abbrev spotCtorAfterParState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ spotCtorOneWord

abbrev spotCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ ⟨1⟩

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

theorem evalExpr_spotCtorLocalVat {evm : EVM.State} (vat : AccountAddress) :
    evalExpr? config { contract := contract, locals := spotCtorLocals vat } evm (.var "vat_") =
      .ok (.address vat) := by
  simp [evalExpr?, spotCtorLocals, EvalResult.ofOption]

theorem assign_spotCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := spotCtorAfterWardsState evm
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
    simpa [evm', spotCtorAfterWardsState] using
      storageLocStore_uint256 evm (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc (wardsSlot (.address evm.executionEnv.source)))
    (hbase := by simpa [wardsRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, storageTypeStep?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

private theorem assign_spotCtorAddressStorage (evm : EVM.State) (locals : Store)
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
        (word_val_addr_canonical addrValue)
  exact assignStorageRef_storage_scalar_value
    (ty := .elem .address) (loc := addrLoc slot)
    (hbase := hbase)
    (her := her)
    (hty := hty)
    (hloc := hloc)
    (hscalar := by trivial)
    (hstore := hstore)

theorem assign_spotCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := spotCtorAfterVatState evm vat
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_spotCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨2⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

private theorem assign_spotCtorUint256Storage (evm : EVM.State) (locals : Store)
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
  simpa [evm'] using storageLocStore_uint256 evm slot value

theorem assign_spotCtorParStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "par" = none) :
    let evm' := spotCtorAfterParState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage parRef (.int one) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [spotCtorAfterParState, spotCtorOneWord_toInt] using
    assign_spotCtorUint256Storage evm locals parRef { base := "par", steps := [] } ⟨3⟩
      spotCtorOneWord
      (by simpa [parRef] using hbase)
      (by simp [parRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_spotCtorLiveStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "live" = none) :
    let evm' := spotCtorAfterLiveState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [spotCtorAfterLiveState] using
    assign_spotCtorUint256Storage evm locals liveRef { base := "live", steps := [] } ⟨4⟩
      ⟨1⟩
      (by simpa [liveRef] using hbase)
      (by simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem spotCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = spotCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot spotCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem spotCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := spotCtorLocals vat
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := spotCtorAfterWardsState evm0
    let evm2 := spotCtorAfterVatState evm1 vat
    let evm3 := spotCtorAfterParState evm2
    let evm4 := spotCtorAfterLiveState evm3
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals } evm4) := by
  intro locals evm0 evm1 evm2 evm3 evm4
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, spotCtorAfterWardsState] using
      assign_spotCtorWardsCaller evm0 (locals := locals) (by simp [locals, spotCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, spotCtorAfterVatState] using
      assign_spotCtorVatStorage evm1 locals vat (by simp [locals, spotCtorLocals])
  have hassignPar :
      assignStorageRef? config { contract := contract, locals := locals } evm2
        .storage parRef (.int one) =
          .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3, spotCtorAfterParState] using
      assign_spotCtorParStorage evm2 locals (by simp [locals, spotCtorLocals])
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm3
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4, spotCtorAfterLiveState] using
      assign_spotCtorLiveStorage evm3 locals (by simp [locals, spotCtorLocals])
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_spotCtorLocalVat (evm := evm1) vat
  refine ExecBlock.consNormal (ExecStmt.assign (by rw [evalExpr?]; rfl) hassignPar) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by rw [evalExpr?]; rfl) hassignLive) ExecBlock.nil

theorem spotSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address vat] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned { contract := contract, locals := spotCtorLocals vat }
        (spotCtorAfterLiveState
          (spotCtorAfterParState
            (spotCtorAfterVatState
              (spotCtorAfterWardsState
                (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I))
              vat)))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := spotCtorLocals vat)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (spotCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) vat hwv)

theorem spotSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address vat] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := spotCtorLocals vat)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := spotCtorLocals vat) hwv

end Benchmarks.Dss.Spot
