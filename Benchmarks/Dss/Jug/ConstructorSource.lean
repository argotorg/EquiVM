import Benchmarks.Dss.Jug.ConstructorBase

/-!
# MakerDAO/Sky DSS Jug constructor Solm source semantics
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Jug

set_option maxRecDepth 2000000

abbrev jugCtorLocals (vat : AccountAddress) : Store :=
  (∅ : Store).insert "vat_" (.address vat)

abbrev jugCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev jugCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (EVM.word vat.val))

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

theorem evalExpr_jugCtorLocalVat {evm : EVM.State} (vat : AccountAddress) :
    evalExpr? config { contract := contract, locals := jugCtorLocals vat } evm (.var "vat_") =
      .ok (.address vat) := by
  simp [evalExpr?, jugCtorLocals, EvalResult.ofOption]

theorem assign_jugCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := jugCtorAfterWardsState evm
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
    simpa [evm', jugCtorAfterWardsState] using
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

private theorem assign_jugCtorAddressStorage (evm : EVM.State) (locals : Store)
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

theorem assign_jugCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := jugCtorAfterVatState evm vat
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_jugCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨2⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem jugCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = jugCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot jugCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem jugCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := jugCtorLocals vat
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := jugCtorAfterWardsState evm0
    let evm2 := jugCtorAfterVatState evm1 vat
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals } evm2) := by
  intro locals evm0 evm1 evm2
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1, jugCtorAfterWardsState] using
      assign_jugCtorWardsCaller evm0 (locals := locals) (by simp [locals, jugCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2, jugCtorAfterVatState] using
      assign_jugCtorVatStorage evm1 locals vat (by simp [locals, jugCtorLocals])
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ExecBlock.nil
  · simpa [locals] using evalExpr_jugCtorLocalVat (evm := evm1) vat

theorem jugSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address vat] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned { contract := contract, locals := jugCtorLocals vat }
        (jugCtorAfterVatState
          (jugCtorAfterWardsState
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I))
          vat)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := jugCtorLocals vat)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (jugCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) vat hwv)

theorem jugSolmCtorExecReverts_nonpayable
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
    (argsStore := jugCtorLocals vat)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := jugCtorLocals vat) hwv

end Benchmarks.Dss.Jug
