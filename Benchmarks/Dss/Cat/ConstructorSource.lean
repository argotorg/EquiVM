import Benchmarks.Dss.Cat.ConstructorBase

/-!
# MakerDAO/Sky DSS Cat constructor Solm source semantics

The Cat constructor stores three slots in order: `wards[sender] = 1`, `vat = vat_` (slot 3, address
pack), `live = 1` (scalar slot 2).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Cat

set_option maxRecDepth 2000000

abbrev catCtorLocals (vat : AccountAddress) : Store :=
  (∅ : Store).insert "vat_" (.address vat)

abbrev catCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev catCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      (EVM.word vat.val))

abbrev catCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩ ⟨1⟩

/-- Full three-store constructor post-state applied to `evm`. -/
abbrev catCtorPostState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  catCtorAfterLiveState (catCtorAfterVatState (catCtorAfterWardsState evm) vat)

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

theorem evalExpr_catCtorLocalVat {evm : EVM.State} (vat : AccountAddress) :
    evalExpr? config { contract := contract, locals := catCtorLocals vat } evm (.var "vat_") =
      .ok (.address vat) := by
  simp [evalExpr?, catCtorLocals, EvalResult.ofOption]

theorem assign_catCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := catCtorAfterWardsState evm
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
    simpa [evm', catCtorAfterWardsState] using
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

private theorem assign_catCtorAddressStorage (evm : EVM.State) (locals : Store)
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

theorem assign_catCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := catCtorAfterVatState evm vat
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_catCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨3⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_catCtorLiveStorage (evm : EVM.State) (locals : Store)
    (hbaseAbsent : locals.get? "live" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, catCtorAfterLiveState evm) := by
  apply assignStorageRef_storage_scalar
    (ty := uint256St) (loc := wordLoc ⟨2⟩) (er := { base := "live", steps := [] })
    (hbase := by simpa [liveRef] using hbaseAbsent)
    (her := by simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
  simpa using storageLocStore_uint256 evm ⟨2⟩ ⟨1⟩

theorem catCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = catCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot catCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem catCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := catCtorLocals vat
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals } (catCtorPostState evm0 vat)) := by
  intro locals evm0
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, catCtorAfterWardsState evm0) := by
    simpa using
      assign_catCtorWardsCaller evm0 (locals := locals) (by simp [locals, catCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals }
        (catCtorAfterWardsState evm0)
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals },
            catCtorAfterVatState (catCtorAfterWardsState evm0) vat) := by
    simpa using
      assign_catCtorVatStorage (catCtorAfterWardsState evm0) locals vat
        (by simp [locals, catCtorLocals])
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_catCtorLocalVat (evm := catCtorAfterWardsState evm0) vat
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assign_catCtorLiveStorage _ locals (by simp [locals, catCtorLocals])))
    ExecBlock.nil

theorem catSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address vat] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned { contract := contract, locals := catCtorLocals vat }
        (catCtorPostState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          vat)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := catCtorLocals vat)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (catCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) vat hwv)

theorem catSolmCtorExecReverts_nonpayable
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
    (argsStore := catCtorLocals vat)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := catCtorLocals vat) hwv

end Benchmarks.Dss.Cat
