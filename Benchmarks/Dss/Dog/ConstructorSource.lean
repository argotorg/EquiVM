import Benchmarks.Dss.Dog.Common

/-!
# MakerDAO/Sky DSS Dog constructor Solm source semantics
-/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Dss.Dog.Immutables

namespace Benchmarks.Dss.Dog

set_option maxRecDepth 2000000

abbrev dogCtorLocals (vat : AccountAddress) : Store :=
  (∅ : Store).insert "vat_" (.address vat)

abbrev dogCtorFinalLocals (vat : AccountAddress) : Store :=
  (dogCtorLocals vat).insert "imm_vat" (.address vat)

abbrev dogCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ ⟨1⟩

abbrev dogCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

theorem dogCtorFinalLocals_get_imm_vat (vat : AccountAddress) :
    (dogCtorFinalLocals vat).get? "imm_vat" = some (.address vat) := by
  rw [dogCtorFinalLocals, store_get_self]

theorem dogCtorRuntimeCodeOf (v : DogImmutables) :
    runtimeCodeOf dogBytecode (dogCtorFinalLocals v.vat) =
      patchRuntime dogBytecode (patches v) := by
  unfold runtimeCodeOf patchesFrom patches immValues
  simp only [offsets, List.foldrM_cons, List.foldrM_nil, pure, bind]
  rw [dogCtorFinalLocals_get_imm_vat v.vat]
  rfl

theorem evalExpr_dogCtorLocalVat {v : DogImmutables} {evm : EVM.State}
    (vat : AccountAddress) :
    evalExpr? (config v) { contract := contract v, locals := dogCtorLocals vat } evm
      (.var "vat_") = .ok (.address vat) := by
  simp [evalExpr?, dogCtorLocals, EvalResult.ofOption]

theorem assign_dogCtorLiveStorage {v : DogImmutables} (evm : EVM.State)
    {locals : Store} (hbase : locals.get? "live" = none) :
    let evm' := dogCtorAfterLiveState evm
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef (config v) { contract := contract v, locals := locals } evm liveRef =
        .ok { base := "live", steps := [] } := by
    simp [liveRef, evalStorageRef, evalStorageRefSteps, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc ⟨3⟩) (.int 1) = some evm' := by
    simpa [evm', dogCtorAfterLiveState] using storageLocStore_uint256 evm ⟨3⟩ ⟨1⟩
  exact assignStorageRef_storage_scalar
    (ty := .elem (.int uint256Int)) (loc := wordLoc ⟨3⟩)
    (hbase := by simpa [liveRef] using hbase)
    (her := her)
    (hty := by simp [storageTypeAt?, contract, storageDecls, uint256St])
    (hloc := by
      funext evm
      simp [config, storageLayout, solidityStorageLayout, storageLayoutRaw])
    (hstore := hstore)

theorem assign_dogCtorWardsCaller {v : DogImmutables} (evm : EVM.State)
    {locals : Store} (hbase : locals.get? "wards" = none) :
    let evm' := dogCtorAfterWardsState evm
    assignStorageRef? (config v) { contract := contract v, locals := locals } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract v, locals := locals }, evm') := by
  intro evm'
  have her :
      evalStorageRef (config v) { contract := contract v, locals := locals } evm
        (wardsRef sender) =
          .ok { base := "wards", steps := [.mindex (.address evm.executionEnv.source)] } := by
    simp [wardsRef, sender, evalStorageRef, evalStorageRefSteps, evalStorageRefStep,
      evalExpr?, envValue, valueToKey?, EvalResult.ofOption, EvalResult.bind, pure, bind]
  have hstore :
      storageLocStore evm (wordLoc (wardsSlot (.address evm.executionEnv.source))) (.int 1) =
        some evm' := by
    simpa [evm', dogCtorAfterWardsState] using
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

theorem dogCtorCallerWardsSlot_eq (I : ExecutionEnv) :
    wardsSlot (.address I.source) = dogCallerWardsSlot I := by
  unfold wardsSlot mapSlot dogCallerWardsSlot solcMappingSlot solcSourceWord
  rw [keyValueToWord_address]

theorem dogCtorBodySuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (v : DogImmutables) (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := dogCtorLocals vat
    let finalLocals := dogCtorFinalLocals vat
    let evm0 := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := dogCtorAfterLiveState evm0
    let evm2 := dogCtorAfterWardsState evm1
    ExecBlock (config v) { contract := contract v, locals := locals }
      evm0 constructorDecl.body (.ok { contract := contract v, locals := finalLocals }
        evm2) := by
  intro locals finalLocals evm0 evm1 evm2
  have hassignLive :
      assignStorageRef? (config v)
          { contract := contract v, locals := finalLocals } evm0
        .storage liveRef (.int 1) =
          .ok ({ contract := contract v, locals := finalLocals }, evm1) := by
    simpa [evm1, dogCtorAfterLiveState, finalLocals, dogCtorFinalLocals] using
      assign_dogCtorLiveStorage (v := v) evm0 (locals := finalLocals)
        (by
          change (dogCtorFinalLocals vat).get? "live" = none
          rw [dogCtorFinalLocals, dogCtorLocals]
          rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
          simp)
  have hassignWards :
      assignStorageRef? (config v)
          { contract := contract v, locals := finalLocals } evm1
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract v, locals := finalLocals }, evm2) := by
    simpa [evm2, dogCtorAfterWardsState, finalLocals, dogCtorFinalLocals] using
      assign_dogCtorWardsCaller (v := v) evm1 (locals := finalLocals)
        (by
          change (dogCtorFinalLocals vat).get? "wards" = none
          rw [dogCtorFinalLocals, dogCtorLocals]
          rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide)]
          simp)
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .address vat) ?_) ?_
  · simpa [locals] using evalExpr_dogCtorLocalVat (v := v) (evm := evm0) vat
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards)
    ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem dogSolmCtorExecSuccess
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (v : DogImmutables) (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec (config v) (contract v) [.address vat] createdAccounts
      genesisBlockHeader blocks σ σ₀ g A I
      (.returned { contract := contract v, locals := dogCtorFinalLocals vat }
        (dogCtorAfterWardsState
          (dogCtorAfterLiveState
            (initState createdAccounts genesisBlockHeader blocks σ σ₀ (Sat256.ofUInt256 g) A I)))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := dogCtorLocals vat) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl] using
      ExecFuncBody.execBlockOK
        (dogCtorBodySuccess
          (createdAccounts := createdAccounts) (genesisBlockHeader := genesisBlockHeader)
          (blocks := blocks) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) v vat hwv)

theorem dogSolmCtorExecReverts_nonpayable
    {createdAccounts : Batteries.RBSet AccountAddress compare}
    {genesisBlockHeader : BlockHeader} {blocks : ProcessedBlocks}
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (v : DogImmutables) (vat : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec (config v) (contract v) [.address vat] createdAccounts
      genesisBlockHeader blocks σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState createdAccounts genesisBlockHeader blocks σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := dogCtorLocals vat) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [ExecTransitionBody, contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config v) (contract := contract v)
        (evm := initState createdAccounts genesisBlockHeader blocks σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := dogCtorLocals vat) hwv

end Benchmarks.Dss.Dog
