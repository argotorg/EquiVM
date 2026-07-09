import Benchmarks.Dss.Pot.ConstructorBase

/-!
# MakerDAO/Sky DSS Pot constructor Solm source semantics

The Pot constructor stores six slots in order: `wards[sender] = 1`, `vat = vat_` (slot 5, address
pack), `dsr = ONE`, `chi = ONE` (slots 3/4), `rho = now` (slot 7), `live = 1` (slot 8).
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Pot

set_option maxRecDepth 2000000

abbrev potCtorLocals (vat : AccountAddress) : Store :=
  (∅ : Store).insert "vat_" (.address vat)

abbrev potCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev potCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨5⟩)
      (EVM.word vat.val))

abbrev potCtorAfterDsrState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ potCtorOne

abbrev potCtorAfterChiState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ potCtorOne

abbrev potCtorAfterRhoState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩
    (UInt256.ofNat evm.executionEnv.header.timestamp)

abbrev potCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨1⟩

/-- Full six-store constructor post-state applied to `evm`. -/
abbrev potCtorPostState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  potCtorAfterLiveState
    (potCtorAfterRhoState
      (potCtorAfterChiState
        (potCtorAfterDsrState
          (potCtorAfterVatState (potCtorAfterWardsState evm) vat))))

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

theorem evalExpr_potCtorLocalVat {evm : EVM.State} (vat : AccountAddress) :
    evalExpr? config { contract := contract, locals := potCtorLocals vat } evm (.var "vat_") =
      .ok (.address vat) := by
  simp [evalExpr?, potCtorLocals, EvalResult.ofOption]

theorem assign_potCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := potCtorAfterWardsState evm
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
    simpa [evm', potCtorAfterWardsState] using
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

private theorem assign_potCtorAddressStorage (evm : EVM.State) (locals : Store)
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

theorem assign_potCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := potCtorAfterVatState evm vat
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_potCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨5⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

/-! ### Scalar stores (`dsr`, `chi`, `rho`, `live`) -/

theorem assign_potCtorDsrStorage (evm : EVM.State) (locals : Store)
    (hbaseAbsent : locals.get? "dsr" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage dsrRef (.int one) =
        .ok ({ contract := contract, locals := locals }, potCtorAfterDsrState evm) := by
  apply assignStorageRef_storage_scalar
    (ty := uint256St) (loc := wordLoc ⟨3⟩) (er := { base := "dsr", steps := [] })
    (hbase := by simpa [dsrRef] using hbaseAbsent)
    (her := by simp [dsrRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  rw [potCtorOne_eq_one]
  exact potStorageLocStore_uint256 evm ⟨3⟩ potCtorOne

theorem assign_potCtorChiStorage (evm : EVM.State) (locals : Store)
    (hbaseAbsent : locals.get? "chi" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage chiRef (.int one) =
        .ok ({ contract := contract, locals := locals }, potCtorAfterChiState evm) := by
  apply assignStorageRef_storage_scalar
    (ty := uint256St) (loc := wordLoc ⟨4⟩) (er := { base := "chi", steps := [] })
    (hbase := by simpa [chiRef] using hbaseAbsent)
    (her := by simp [chiRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  rw [potCtorOne_eq_one]
  exact potStorageLocStore_uint256 evm ⟨4⟩ potCtorOne

theorem assign_potCtorRhoStorage (evm : EVM.State) (locals : Store)
    (hbaseAbsent : locals.get? "rho" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage rhoRef
        (.int (Int.ofNat (UInt256.ofNat evm.executionEnv.header.timestamp).toNat)) =
        .ok ({ contract := contract, locals := locals }, potCtorAfterRhoState evm) := by
  apply assignStorageRef_storage_scalar
    (ty := uint256St) (loc := wordLoc ⟨7⟩) (er := { base := "rho", steps := [] })
    (hbase := by simpa [rhoRef] using hbaseAbsent)
    (her := by simp [rhoRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  exact potStorageLocStore_uint256 evm ⟨7⟩
    (UInt256.ofNat evm.executionEnv.header.timestamp)

theorem assign_potCtorLiveStorage (evm : EVM.State) (locals : Store)
    (hbaseAbsent : locals.get? "live" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, potCtorAfterLiveState evm) := by
  apply assignStorageRef_storage_scalar
    (ty := uint256St) (loc := wordLoc ⟨8⟩) (er := { base := "live", steps := [] })
    (hbase := by simpa [liveRef] using hbaseAbsent)
    (her := by simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by rfl)
  simpa using potStorageLocStore_uint256 evm ⟨8⟩ ⟨1⟩

theorem potCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = potCtorCallerWardsSlot I := by
  unfold wardsSlot mapSlot potCtorCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem potCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := potCtorLocals vat
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals } (potCtorPostState evm0 vat)) := by
  intro locals evm0
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, potCtorAfterWardsState evm0) := by
    simpa using
      assign_potCtorWardsCaller evm0 (locals := locals) (by simp [locals, potCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals }
        (potCtorAfterWardsState evm0)
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals },
            potCtorAfterVatState (potCtorAfterWardsState evm0) vat) := by
    simpa using
      assign_potCtorVatStorage (potCtorAfterWardsState evm0) locals vat
        (by simp [locals, potCtorLocals])
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_potCtorLocalVat (evm := potCtorAfterWardsState evm0) vat
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assign_potCtorDsrStorage _ locals (by simp [locals, potCtorLocals]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assign_potCtorChiStorage _ locals (by simp [locals, potCtorLocals]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign ?_
      (assign_potCtorRhoStorage _ locals (by simp [locals, potCtorLocals]))) ?_
  · simp [evalExpr?, envValue, pure]
  exact ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assign_potCtorLiveStorage _ locals (by simp [locals, potCtorLocals])))
    ExecBlock.nil

theorem potSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address vat] createdAccounts genesisBlockHeader blocks
      σ σ₀ g A I
      (.returned { contract := contract, locals := potCtorLocals vat }
        (potCtorPostState
          (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)
          vat)
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := potCtorLocals vat)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (potCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) vat hwv)

theorem potSolmCtorExecReverts_nonpayable
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
    (argsStore := potCtorLocals vat)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := potCtorLocals vat) hwv

end Benchmarks.Dss.Pot
