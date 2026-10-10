import Benchmarks.Morpho.MetaMorphoV1_1.PackedDeletion

/-! The timelock setter stores its value, emits its event, and clears the pending record. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

abbrev setTimelockFunction : FunctionDecl := contract.functions[2]!

def setTimelockFrame (imms : Store) (value : UInt256) : Frame :=
  { contract := contract
    locals := (∅ : Store).insert "newTimelock" (uint256Value value)
    immutables := imms }

def setTimelockValueState (evm : EVM.State) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨14⟩ value

def setTimelockState (evm : EVM.State) (value : UInt256) : EVM.State :=
  let changed := setTimelockValueState evm value
  Solm.EVM.storageStore changed changed.executionEnv.codeOwner ⟨17⟩ ⟨0⟩

def setTimelockFinalFrame (evm : EVM.State) (imms : Store) (value : UInt256) : Frame :=
  { contract := contract
    locals := (setTimelockFrame imms value).locals.insert "__c0"
      (.address (setTimelockValueState evm value).executionEnv.source)
    immutables := imms }

theorem setTimelockAssign (evm : EVM.State) (imms : Store) (value : UInt256) :
    ExecStmt config (setTimelockFrame imms value) evm
      (.assign .storage ⟨"timelock", []⟩ (.var "newTimelock"))
      (.ok (setTimelockFrame imms value) (setTimelockValueState evm value)) := by
  apply ExecStmt.assign (value := uint256Value value)
  · simp [evalExpr?, setTimelockFrame, EvalResult.ofOption]
  · exact assignStorageRef_storage_scalar_value (er := ⟨"timelock", []⟩)
      (ty := .elem (.int (.uint ⟨256, by decide⟩)))
      (by simp [setTimelockFrame])
      (by simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
      rfl rfl rfl (.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm ⟨14⟩ value)

theorem setTimelockBody (evm : EVM.State) (imms : Store) (value : UInt256) :
    ExecFuncBody config (setTimelockFrame imms value) evm setTimelockFunction.body
      (.returned (setTimelockFinalFrame evm imms value) (setTimelockState evm value) none) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (setTimelockAssign evm imms value) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address (setTimelockValueState evm value).executionEnv.source)
      rfl (by simp only [evalExpr?, envValue, pure])) ?_
  apply (ABlock.start.emitStep (vals := [
    .address (setTimelockValueState evm value).executionEnv.source, uint256Value value]) ?_).run
  · exact ExecBlock.consNormal (ExecStmt.delete (deleteStorage_pendingTimelock _ _ imms
      (by simp [setTimelockFrame]))) ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, setTimelockFrame, store_get_self,
      store_get_ne _ _ (by decide : ("__c0" == "newTimelock") = false),
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem setTimelockBodyStatic (evm : EVM.State) (imms : Store) (value : UInt256)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (setTimelockFrame imms value) evm setTimelockFunction.body
      .staticViolation := by
  exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic
    (execStmt_assign_static (setTimelockAssign evm imms value) hperm))

theorem setTimelockCall (evm : EVM.State) (locals imms : Store) (value : UInt256)
    (arg : Expr) (retVar : Ident)
    (heval : evalExpr? config ⟨contract, locals, imms⟩ evm arg = .ok (uint256Value value)) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_setTimelock" [arg] retVar)
      (.ok ⟨contract, locals.insert retVar .unit, imms⟩ (setTimelockState evm value)) := by
  exact internalCallFunctionReturn (caller := ⟨contract, locals, imms⟩)
    (callee := setTimelockFunction) (argVals := [uint256Value value]) (value := none)
    (by simp only [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (setTimelockBody evm imms value)

theorem setTimelockCallStatic (evm : EVM.State) (locals imms : Store) (value : UInt256)
    (arg : Expr) (retVar : Ident)
    (heval : evalExpr? config ⟨contract, locals, imms⟩ evm arg = .ok (uint256Value value))
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "_setTimelock" [arg] retVar)
      .staticViolation := by
  exact ExecStmt.internalCallStatic (callee := setTimelockFunction.toCallable)
    (argVals := [uint256Value value])
    (by simp only [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (setTimelockBodyStatic evm imms value hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
