import Benchmarks.Morpho.MetaMorphoV1_1.CuratorRoleSource
import Benchmarks.Morpho.MetaMorphoV1_1.AllocatorMutation

/-! Authorization by an allocator, the curator, or the owner. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

abbrev allocatorRoleAllowed (evm : EVM.State) : Prop :=
  allocatorByte evm evm.executionEnv.source ≠ ⟨0⟩ ∨ curatorRoleAllowed evm

abbrev allocatorRoleFunction : FunctionDecl := contract.functions[7]!

def allocatorRoleCondition : Expr :=
  .binary .or (.storage ⟨"isAllocator", [.mindex (.var "sender")]⟩) curatorRoleCondition

theorem allocatorRoleComparison (evm : EVM.State) (imms : Store) :
    evalExpr? config (guardianRoleFrame evm imms) evm allocatorRoleCondition =
      .ok (.bool (decide (allocatorRoleAllowed evm))) := by
  have ha := evalStorage_allocator evm ((∅ : Store).insert "sender"
    (.address evm.executionEnv.source)) imms "sender" evm.executionEnv.source
    (by simp) (store_get_self _ _ _)
  rw [wordToElemBool] at ha
  have he := evalExpr_boolOr ha (curatorRoleComparison evm imms)
  simpa only [allocatorRoleCondition, allocatorRoleAllowed, Bool.decide_or, decide_not] using he

theorem allocatorRolePrefix (evm : EVM.State) (imms : Store) :
    ABlock config evm { contract := contract, locals := ∅, immutables := imms }
      allocatorRoleFunction.body (guardianRoleFrame evm imms)
      [.require allocatorRoleCondition] := by
  constructor
  intro result htail
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (by simp [evalExpr?, envValue, pure])) htail

theorem allocatorRoleBodyReturns (evm : EVM.State) (imms : Store)
    (hrole : allocatorRoleAllowed evm) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms } evm
      allocatorRoleFunction.body (.returned (guardianRoleFrame evm imms) evm none) := by
  apply ExecFuncBody.execBlockOK
  apply ((allocatorRolePrefix evm imms).requireStep (by
    simp only [allocatorRoleComparison, hrole, decide_true])).run
  exact ExecBlock.nil

theorem allocatorRoleBodyReverts (evm : EVM.State) (imms : Store)
    (hrole : ¬ allocatorRoleAllowed evm) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms } evm
      allocatorRoleFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact (allocatorRolePrefix evm imms).requireRevert (by
    simp only [allocatorRoleComparison, hrole, decide_false])

theorem allocatorRoleCall (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (hrole : allocatorRoleAllowed evm) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkAllocatorRole" [] retVar)
      (.ok { contract := contract, locals := locals.insert retVar .unit, immutables := imms }
        evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := allocatorRoleFunction) (value := none) rfl rfl rfl
    (allocatorRoleBodyReturns evm imms hrole)

theorem allocatorRoleCallReverts (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (hrole : ¬ allocatorRoleAllowed evm) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkAllocatorRole" [] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := allocatorRoleFunction) rfl rfl rfl
    (allocatorRoleBodyReverts evm imms hrole)

end Benchmarks.Morpho.MetaMorphoV1_1
