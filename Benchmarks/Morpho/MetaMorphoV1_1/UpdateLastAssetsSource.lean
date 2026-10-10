import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon

/-! The last-total-assets update used by interest accrual. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

abbrev updateLastAssetsFunction : FunctionDecl := contract.functions[47]!

def updateLastAssetsState (evm : EVM.State) (value : UInt256) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨22⟩ value

def updateLastAssetsFrame (imms : Store) (value : UInt256) : Frame :=
  ⟨contract, (∅ : Store).insert "updatedTotalAssets" (uint256Value value), imms⟩

theorem updateLastAssetsAssign (evm : EVM.State) (imms : Store) (value : UInt256) :
    ExecStmt config (updateLastAssetsFrame imms value) evm
      (.assign .storage ⟨"lastTotalAssets", []⟩ (.var "updatedTotalAssets"))
      (.ok (updateLastAssetsFrame imms value) (updateLastAssetsState evm value)) := by
  apply ExecStmt.assign (value := uint256Value value)
  · simp only [evalExpr?, updateLastAssetsFrame, store_get_self, EvalResult.ofOption]
  · exact assignStorageRef_storage_scalar_value (er := ⟨"lastTotalAssets", []⟩)
      (ty := .elem (.int (.uint ⟨256, by decide⟩))) (by simp [updateLastAssetsFrame])
      (by simp [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure])
      rfl rfl rfl (.inl ⟨_, rfl⟩) (storageLocStore_uint256 evm ⟨22⟩ value)

theorem updateLastAssetsBody (evm : EVM.State) (imms : Store) (value : UInt256) :
    ExecFuncBody config (updateLastAssetsFrame imms value) evm updateLastAssetsFunction.body
      (.returned (updateLastAssetsFrame imms value) (updateLastAssetsState evm value) none) := by
  apply ExecFuncBody.execBlockOK
  refine ExecBlock.consNormal (updateLastAssetsAssign evm imms value) ?_
  apply (ABlock.start.emitStep (vals := [uint256Value value]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, updateLastAssetsFrame, store_get_self,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem updateLastAssetsBodyStatic (evm : EVM.State) (imms : Store) (value : UInt256)
    (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (updateLastAssetsFrame imms value) evm updateLastAssetsFunction.body
      .staticViolation := by
  exact ExecFuncBody.execBlockStatic (ExecBlock.consStatic
    (execStmt_assign_static (updateLastAssetsAssign evm imms value) hperm))

theorem updateLastAssetsCall (evm : EVM.State) (locals imms : Store) (value : UInt256)
    (arg : Expr) (retVar : Ident)
    (heval : evalExpr? config ⟨contract, locals, imms⟩ evm arg = .ok (uint256Value value)) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall "_updateLastTotalAssets" [arg] retVar)
      (.ok ⟨contract, locals.insert retVar .unit, imms⟩ (updateLastAssetsState evm value)) := by
  exact internalCallFunctionReturn (caller := ⟨contract, locals, imms⟩)
    (callee := updateLastAssetsFunction) (argVals := [uint256Value value]) (value := none)
    (by simp only [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (updateLastAssetsBody evm imms value)

theorem updateLastAssetsCallStatic (evm : EVM.State) (locals imms : Store) (value : UInt256)
    (arg : Expr) (retVar : Ident)
    (heval : evalExpr? config ⟨contract, locals, imms⟩ evm arg = .ok (uint256Value value))
    (hperm : evm.executionEnv.perm = false) :
    ExecStmt config ⟨contract, locals, imms⟩ evm
      (.internalCall "_updateLastTotalAssets" [arg] retVar)
      .staticViolation := by
  exact ExecStmt.internalCallStatic (callee := updateLastAssetsFunction.toCallable)
    (argVals := [uint256Value value])
    (by simp only [evalExprs?, heval, bind, EvalResult.bind, pure]) rfl rfl
    (updateLastAssetsBodyStatic evm imms value hperm)

end Benchmarks.Morpho.MetaMorphoV1_1
