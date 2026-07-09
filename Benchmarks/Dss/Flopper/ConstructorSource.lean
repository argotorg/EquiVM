import Benchmarks.Dss.Flopper.ConstructorBase
import Benchmarks.Dss.Flopper.File
import Reasoning.ExternalCall

/-!
# MakerDAO/Sky DSS Flopper constructor Solm source semantics
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Dss.Flopper

set_option maxRecDepth 2000000

abbrev flopperCtorLocals (vat gem : AccountAddress) : Store :=
  ((∅ : Store).insert "vat_" (.address vat)).insert "gem_" (.address gem)

abbrev flopperCtorAfterBegState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨4⟩ flopperCtorBegWord

abbrev flopperCtorAfterPadState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨5⟩ flopperCtorPadWord

abbrev flopperCtorAfterTtlState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (fileSetUint48Offset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
      flopperCtorTtlWord)

abbrev flopperCtorAfterTauState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨6⟩
    (fileSetUint48Offset6Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨6⟩)
      flopperCtorTauWord)

abbrev flopperCtorAfterKicksState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨7⟩ ⟨0⟩

abbrev flopperCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

abbrev flopperCtorAfterVatState (evm : EVM.State) (vat : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨2⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨2⟩)
      (EVM.word vat.val))

abbrev flopperCtorAfterGemState (evm : EVM.State) (gem : AccountAddress) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩
    (setAddressOffset0Word (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨3⟩)
      (EVM.word gem.val))

abbrev flopperCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨8⟩ ⟨1⟩

private theorem accountAddress_of_word_val (a : AccountAddress) :
    AccountAddress.ofNat (EVM.word a.val).toNat = a := by
  rw [← accountAddress_ofUInt256_eq_ofNat_toNat]
  exact accountAddress_roundtrip a

theorem evalExpr_flopperCtorLocalVat {evm : EVM.State} (vat gem : AccountAddress) :
    evalExpr? config { contract := contract, locals := flopperCtorLocals vat gem } evm
      (.var "vat_") = .ok (.address vat) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [flopperCtorLocals, store_get_ne _ _ (by decide), store_get_self]

theorem evalExpr_flopperCtorLocalGem {evm : EVM.State} (vat gem : AccountAddress) :
    evalExpr? config { contract := contract, locals := flopperCtorLocals vat gem } evm
      (.var "gem_") = .ok (.address gem) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [flopperCtorLocals, store_get_self]

theorem assign_flopperCtorWardsCaller (evm : EVM.State) {locals : Store}
    (hbase : locals.get? "wards" = none) :
    let evm' := flopperCtorAfterWardsState evm
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
    simpa [evm', flopperCtorAfterWardsState] using
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

private theorem assign_flopperCtorUint256Storage (evm : EVM.State) (locals : Store)
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

theorem assign_flopperCtorBegStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "beg" = none) :
    let evm' := flopperCtorAfterBegState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage begRef (.int defaultBeg) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [flopperCtorAfterBegState, defaultBeg] using
    assign_flopperCtorUint256Storage evm locals begRef { base := "beg", steps := [] } ⟨4⟩
      flopperCtorBegWord
      (by simpa [begRef] using hbase)
      (by simp [begRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_flopperCtorPadStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "pad" = none) :
    let evm' := flopperCtorAfterPadState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage padRef (.int defaultPad) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [flopperCtorAfterPadState, defaultPad] using
    assign_flopperCtorUint256Storage evm locals padRef { base := "pad", steps := [] } ⟨5⟩
      flopperCtorPadWord
      (by simpa [padRef] using hbase)
      (by simp [padRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_flopperCtorTtlStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "ttl" = none) :
    let evm' := flopperCtorAfterTtlState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage ttlRef (.int defaultTtl) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := { base := "ttl", steps := [] })
      (loc := uint48Loc ⟨6⟩ ⟨0, by decide⟩ (by decide))
      (hbase := by simpa [ttlRef] using hbase)
      (her := by simp [ttlRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
      (hloc := by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
  simpa [evm', flopperCtorAfterTtlState, defaultTtl, uint48Modulus] using
    storageLocStore_uint48_offset0_word evm ⟨6⟩ flopperCtorTtlWord

theorem assign_flopperCtorTauStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "tau" = none) :
    let evm' := flopperCtorAfterTauState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage tauRef (.int defaultTau) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  intro evm'
  apply assignStorageRef_storage_scalar
      (ty := uint48St)
      (er := { base := "tau", steps := [] })
      (loc := uint48Loc ⟨6⟩ ⟨6, by decide⟩ (by decide))
      (hbase := by simpa [tauRef] using hbase)
      (her := by simp [tauRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (hty := by simp [storageTypeAt?, contract, storageDecls, uint48St])
      (hloc := by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
  simpa [evm', flopperCtorAfterTauState, defaultTau, uint48Modulus] using
    storageLocStore_uint48_offset6_word evm ⟨6⟩ flopperCtorTauWord

private theorem assign_flopperCtorAddressStorage (evm : EVM.State) (locals : Store)
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

theorem assign_flopperCtorVatStorage (evm : EVM.State) (locals : Store)
    (vat : AccountAddress) (hbase : locals.get? "vat" = none) :
    let evm' := flopperCtorAfterVatState evm vat
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage vatRef (.address vat) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_flopperCtorAddressStorage evm locals vatRef { base := "vat", steps := [] } ⟨2⟩ vat
    (by simpa [vatRef] using hbase)
    (by simp [vatRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_flopperCtorGemStorage (evm : EVM.State) (locals : Store)
    (gem : AccountAddress) (hbase : locals.get? "gem" = none) :
    let evm' := flopperCtorAfterGemState evm gem
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage gemRef (.address gem) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  exact assign_flopperCtorAddressStorage evm locals gemRef { base := "gem", steps := [] } ⟨3⟩ gem
    (by simpa [gemRef] using hbase)
    (by simp [gemRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
    (by simp [storageTypeAt?, contract, storageDecls, addrSt])
    (by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_flopperCtorLiveStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "live" = none) :
    let evm' := flopperCtorAfterLiveState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [flopperCtorAfterLiveState] using
    assign_flopperCtorUint256Storage evm locals liveRef { base := "live", steps := [] } ⟨8⟩
      ⟨1⟩
      (by simpa [liveRef] using hbase)
      (by simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem assign_flopperCtorKicksStorage (evm : EVM.State) (locals : Store)
    (hbase : locals.get? "kicks" = none) :
    let evm' := flopperCtorAfterKicksState evm
    assignStorageRef? config { contract := contract, locals := locals } evm
      .storage kicksRef (.int 0) =
        .ok ({ contract := contract, locals := locals }, evm') := by
  simpa [flopperCtorAfterKicksState] using
    assign_flopperCtorUint256Storage evm locals kicksRef { base := "kicks", steps := [] } ⟨7⟩
      ⟨0⟩
      (by simpa [kicksRef] using hbase)
      (by simp [kicksRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind])
      (by simp [storageTypeAt?, contract, storageDecls, uint256St])
      (by
        funext evm
        simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])

theorem flopperCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat gem : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := flopperCtorLocals vat gem
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := flopperCtorAfterBegState evm0
    let evm2 := flopperCtorAfterPadState evm1
    let evm3 := flopperCtorAfterTtlState evm2
    let evm4 := flopperCtorAfterTauState evm3
    let evm5 := flopperCtorAfterKicksState evm4
    let evm6 := flopperCtorAfterWardsState evm5
    let evm7 := flopperCtorAfterVatState evm6 vat
    let evm8 := flopperCtorAfterGemState evm7 gem
    let evm9 := flopperCtorAfterLiveState evm8
    ExecBlock config { contract := contract, locals := locals } evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals } evm9) := by
  intro locals evm0 evm1 evm2 evm3 evm4 evm5 evm6 evm7 evm8 evm9
  have hassignBeg :
      assignStorageRef? config { contract := contract, locals := locals } evm0
        .storage begRef (.int defaultBeg) =
          .ok ({ contract := contract, locals := locals }, evm1) := by
    simpa [evm1] using
      assign_flopperCtorBegStorage evm0 locals (by simp [locals, flopperCtorLocals])
  have hassignPad :
      assignStorageRef? config { contract := contract, locals := locals } evm1
        .storage padRef (.int defaultPad) =
          .ok ({ contract := contract, locals := locals }, evm2) := by
    simpa [evm2] using
      assign_flopperCtorPadStorage evm1 locals (by simp [locals, flopperCtorLocals])
  have hassignTtl :
      assignStorageRef? config { contract := contract, locals := locals } evm2
        .storage ttlRef (.int defaultTtl) =
          .ok ({ contract := contract, locals := locals }, evm3) := by
    simpa [evm3] using
      assign_flopperCtorTtlStorage evm2 locals (by simp [locals, flopperCtorLocals])
  have hassignTau :
      assignStorageRef? config { contract := contract, locals := locals } evm3
        .storage tauRef (.int defaultTau) =
          .ok ({ contract := contract, locals := locals }, evm4) := by
    simpa [evm4] using
      assign_flopperCtorTauStorage evm3 locals (by simp [locals, flopperCtorLocals])
  have hassignWards :
      assignStorageRef? config { contract := contract, locals := locals } evm5
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm6) := by
    simpa [evm6] using
      assign_flopperCtorWardsCaller evm5 (locals := locals)
        (by simp [locals, flopperCtorLocals])
  have hassignKicks :
      assignStorageRef? config { contract := contract, locals := locals } evm4
        .storage kicksRef (.int 0) =
          .ok ({ contract := contract, locals := locals }, evm5) := by
    simpa [evm5] using
      assign_flopperCtorKicksStorage evm4 locals (by simp [locals, flopperCtorLocals])
  have hassignVat :
      assignStorageRef? config { contract := contract, locals := locals } evm6
        .storage vatRef (.address vat) =
          .ok ({ contract := contract, locals := locals }, evm7) := by
    simpa [evm7] using
      assign_flopperCtorVatStorage evm6 locals vat (by simp [locals, flopperCtorLocals])
  have hassignGem :
      assignStorageRef? config { contract := contract, locals := locals } evm7
        .storage gemRef (.address gem) =
          .ok ({ contract := contract, locals := locals }, evm8) := by
    simpa [evm8] using
      assign_flopperCtorGemStorage evm7 locals gem (by simp [locals, flopperCtorLocals])
  have hassignLive :
      assignStorageRef? config { contract := contract, locals := locals } evm8
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals }, evm9) := by
    simpa [evm9] using
      assign_flopperCtorLiveStorage evm8 locals (by simp [locals, flopperCtorLocals])
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure, defaultBeg]) hassignBeg) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure, defaultPad]) hassignPad) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure, defaultTtl]) hassignTtl) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure, defaultTau]) hassignTau) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignKicks) ?_
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards) ?_
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignVat) ?_
  · simpa [locals] using evalExpr_flopperCtorLocalVat (evm := evm6) vat gem
  refine ExecBlock.consNormal (ExecStmt.assign ?_ hassignGem) ?_
  · simpa [locals] using evalExpr_flopperCtorLocalGem (evm := evm7) vat gem
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive)
    ExecBlock.nil

theorem flopperSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat gem : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address vat, .address gem] createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I
      (.returned { contract := contract, locals := flopperCtorLocals vat gem }
        (flopperCtorAfterLiveState
          (flopperCtorAfterGemState
            (flopperCtorAfterVatState
              (flopperCtorAfterWardsState
                (flopperCtorAfterKicksState
                  (flopperCtorAfterTauState
                    (flopperCtorAfterTtlState
                      (flopperCtorAfterPadState
                        (flopperCtorAfterBegState
                          (initState createdAccounts genesisBlockHeader blocks σ σ₀
                            (Sat256.ofUInt256 g) A I)))))))
              vat)
            gem))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := flopperCtorLocals vat gem)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (flopperCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          vat gem hwv)

theorem flopperSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat gem : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address vat, .address gem] createdAccounts genesisBlockHeader
      blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := flopperCtorLocals vat gem)
    ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := flopperCtorLocals vat gem) hwv

end Benchmarks.Dss.Flopper
