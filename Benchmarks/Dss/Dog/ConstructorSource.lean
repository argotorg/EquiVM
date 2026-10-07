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

/-- The constructor's final immutables: `vat` set to the argument. -/
abbrev dogCtorFinalImms (vat : AccountAddress) : Store :=
  (initialImmutables contract).insert "vat" (.address vat)

abbrev dogCtorAfterLiveState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨3⟩ ⟨1⟩

abbrev dogCtorAfterWardsState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner
    (wardsSlot (.address evm.executionEnv.source)) ⟨1⟩

theorem evalExpr_dogCtorLocalVat {imms : Store} {evm : EVM.State}
    (vat : AccountAddress) :
    evalExpr? config { contract := contract, locals := dogCtorLocals vat, immutables := imms } evm
      (.var "vat_") = .ok (.address vat) := by
  simp [evalExpr?, dogCtorLocals, EvalResult.ofOption]

theorem assign_dogCtorLiveStorage {imms : Store} (evm : EVM.State)
    {locals : Store} (hbase : locals.get? "live" = none) :
    let evm' := dogCtorAfterLiveState evm
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage liveRef (.int 1) =
        .ok ({ contract := contract, locals := locals, immutables := imms }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals, immutables := imms } evm liveRef =
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

theorem assign_dogCtorWardsCaller {imms : Store} (evm : EVM.State)
    {locals : Store} (hbase : locals.get? "wards" = none) :
    let evm' := dogCtorAfterWardsState evm
    assignStorageRef? config { contract := contract, locals := locals, immutables := imms } evm
      .storage (wardsRef sender) (.int 1) =
        .ok ({ contract := contract, locals := locals, immutables := imms }, evm') := by
  intro evm'
  have her :
      evalStorageRef config { contract := contract, locals := locals, immutables := imms } evm
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
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    let locals := dogCtorLocals vat
    let evm0 := initState σ σ₀
      (Sat256.ofUInt256 g) A I
    let evm1 := dogCtorAfterLiveState evm0
    let evm2 := dogCtorAfterWardsState evm1
    ExecBlock config
      { contract := contract, locals := locals, immutables := initialImmutables contract }
      evm0 constructorDecl.body
      (.ok { contract := contract, locals := locals, immutables := dogCtorFinalImms vat }
        evm2) := by
  intro locals evm0 evm1 evm2
  have hassignLive :
      assignStorageRef? config
          { contract := contract, locals := locals, immutables := dogCtorFinalImms vat } evm0
        .storage liveRef (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := dogCtorFinalImms vat },
            evm1) := by
    simpa [evm1, dogCtorAfterLiveState] using
      assign_dogCtorLiveStorage (imms := dogCtorFinalImms vat) evm0 (locals := locals)
        (by
          change (dogCtorLocals vat).get? "live" = none
          rw [dogCtorLocals, store_get_ne _ _ (by decide)]
          simp)
  have hassignWards :
      assignStorageRef? config
          { contract := contract, locals := locals, immutables := dogCtorFinalImms vat } evm1
        .storage (wardsRef sender) (.int 1) =
          .ok ({ contract := contract, locals := locals, immutables := dogCtorFinalImms vat },
            evm2) := by
    simpa [evm2, dogCtorAfterWardsState] using
      assign_dogCtorWardsCaller (imms := dogCtorFinalImms vat) evm1 (locals := locals)
        (by
          change (dogCtorLocals vat).get? "wards" = none
          rw [dogCtorLocals, store_get_ne _ _ (by decide)]
          simp)
  simp only [constructorDecl, nonpayable, List.cons_append, List.nil_append]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · exact evalCallvalueEq_true (by simp [evm0, initState]; exact hwv)
  refine ExecBlock.consNormal
    (ExecStmt.setImmutable (value := .address vat) (ty := .address) ?_ rfl rfl) ?_
  · simpa [locals] using evalExpr_dogCtorLocalVat (evm := evm0) vat
  refine ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignLive) ?_
  exact ExecBlock.consNormal (ExecStmt.assign (by simp [evalExpr?, pure]) hassignWards)
    ExecBlock.nil

set_option maxHeartbeats 1000000 in
theorem dogSolmCtorExecSuccess
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue = ⟨0⟩) :
    solmCtorExec config contract [.address vat] σ σ₀ g A I
      (.returned
        { contract := contract, locals := dogCtorLocals vat, immutables := dogCtorFinalImms vat }
        (dogCtorAfterWardsState
          (dogCtorAfterLiveState
            (initState σ σ₀ (Sat256.ofUInt256 g) A I)))
        none) := by
  refine solmCtorExec.intro
    (evmState := initState σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := dogCtorLocals vat) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · exact ExecFuncBody.execBlockOK
      (dogCtorBodySuccess (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) vat hwv)

theorem dogSolmCtorExecReverts_nonpayable
    {σ : AccountMap} {σ₀ : AccountMap} {A : Substate} {I : ExecutionEnv}
    {g : UInt256} (vat : AccountAddress)
    (hwv : I.weiValue ≠ ⟨0⟩) :
    solmCtorExec config contract [.address vat] σ σ₀ g A I .reverted := by
  refine solmCtorExec.intro
    (evmState := initState σ σ₀
      (Sat256.ofUInt256 g) A I)
    (argsStore := dogCtorLocals vat) ?_ rfl ?_ ?_
  · rfl
  · rfl
  · simpa [contract, constructorDecl, nonpayable] using
      bodyReverts_nonPayable (cfg := config) (contract := contract)
        (imms := initialImmutables contract)
        (evm := initState σ σ₀
          (Sat256.ofUInt256 g) A I)
        (locals := dogCtorLocals vat) hwv

end Benchmarks.Dss.Dog
