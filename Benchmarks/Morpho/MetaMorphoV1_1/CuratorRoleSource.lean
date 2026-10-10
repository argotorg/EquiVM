import Benchmarks.Morpho.MetaMorphoV1_1.CuratorGuardianSource

/-! Authorization by the curator or owner. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

abbrev curatorRoleAllowed (evm : EVM.State) : Prop :=
  curatorAddress evm = evm.executionEnv.source ∨ ownerAddress evm = evm.executionEnv.source

abbrev curatorRoleFunction : FunctionDecl := contract.functions[8]!

def curatorRoleCondition : Expr :=
  .binary .or (.binary .eq (.var "sender") (.storage ⟨"curator", []⟩))
    (.binary .eq (.var "sender") (.storage ⟨"_owner", []⟩))

theorem curatorRoleComparison (evm : EVM.State) (imms : Store) :
    evalExpr? config (guardianRoleFrame evm imms) evm curatorRoleCondition =
      .ok (.bool (decide (curatorRoleAllowed evm))) := by
  have hs : evalExpr? config (guardianRoleFrame evm imms) evm (.var "sender") =
      .ok (.address evm.executionEnv.source) := by
    simp [evalExpr?, guardianRoleFrame, EvalResult.ofOption]
  have ho := evalExpr_addressEq hs (evalStorage_owner evm _ imms (by simp))
  have hc := evalExpr_addressEq hs (evalStorage_curator evm _ imms (by simp))
  have he := evalExpr_boolOr hc ho
  simpa [curatorRoleCondition, curatorRoleAllowed, curatorAddress,
    ownerAddress, eq_comm] using he

theorem curatorRolePrefix (evm : EVM.State) (imms : Store) :
    ABlock config evm { contract := contract, locals := ∅, immutables := imms }
      curatorRoleFunction.body (guardianRoleFrame evm imms)
      [.require curatorRoleCondition] := by
  constructor
  intro result htail
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (by simp [evalExpr?, envValue, pure])) htail

theorem curatorRoleBodyReturns (evm : EVM.State) (imms : Store)
    (hrole : curatorRoleAllowed evm) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms } evm
      curatorRoleFunction.body (.returned (guardianRoleFrame evm imms) evm none) := by
  apply ExecFuncBody.execBlockOK
  apply ((curatorRolePrefix evm imms).requireStep (by
    simp only [curatorRoleComparison, hrole, decide_true])).run
  exact ExecBlock.nil

theorem curatorRoleBodyReverts (evm : EVM.State) (imms : Store)
    (hrole : ¬ curatorRoleAllowed evm) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms } evm
      curatorRoleFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact (curatorRolePrefix evm imms).requireRevert (by
    simp only [curatorRoleComparison, hrole, decide_false])

theorem curatorRoleCall (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (hrole : curatorRoleAllowed evm) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkCuratorRole" [] retVar)
      (.ok { contract := contract, locals := locals.insert retVar .unit, immutables := imms }
        evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := curatorRoleFunction) (value := none) rfl rfl rfl
    (curatorRoleBodyReturns evm imms hrole)

theorem curatorRoleCallReverts (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (hrole : ¬ curatorRoleAllowed evm) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkCuratorRole" [] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := curatorRoleFunction) rfl rfl rfl
    (curatorRoleBodyReverts evm imms hrole)

end Benchmarks.Morpho.MetaMorphoV1_1
