import Benchmarks.Morpho.MetaMorphoV1_1.GuardianRoleSource

/-! Authorization by the guardian, curator, or owner. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def curatorAddress (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat (UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨10⟩) solcAddrMask).toNat

abbrev curatorGuardianAllowed (evm : EVM.State) : Prop :=
  guardianAddress evm = evm.executionEnv.source ∨
    curatorAddress evm = evm.executionEnv.source ∨ ownerAddress evm = evm.executionEnv.source

abbrev curatorGuardianFunction : FunctionDecl := contract.functions[9]!

def curatorGuardianCondition : Expr :=
  .binary .or (.binary .eq (.var "sender") (.storage ⟨"guardian", []⟩))
    (.binary .or (.binary .eq (.var "sender") (.storage ⟨"curator", []⟩))
      (.binary .eq (.var "sender") (.storage ⟨"_owner", []⟩)))

theorem evalExpr_boolOr {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Bool}
    (ha : evalExpr? cfg solm evm lhs = .ok (.bool a))
    (hb : evalExpr? cfg solm evm rhs = .ok (.bool b)) :
    evalExpr? cfg solm evm (.binary .or lhs rhs) = .ok (.bool (a || b)) := by
  rw [evalExpr?]
  simp only [ha, bind, EvalResult.bind]
  cases a <;> simp [hb, pure]

theorem curatorGuardianComparison (evm : EVM.State) (imms : Store) :
    evalExpr? config (guardianRoleFrame evm imms) evm curatorGuardianCondition =
      .ok (.bool (decide (curatorGuardianAllowed evm))) := by
  have hs : evalExpr? config (guardianRoleFrame evm imms) evm (.var "sender") =
      .ok (.address evm.executionEnv.source) := by
    simp [evalExpr?, guardianRoleFrame, EvalResult.ofOption]
  have ho := evalExpr_addressEq hs (evalStorage_owner evm _ imms (by simp))
  have hc := evalExpr_addressEq hs (evalStorage_curator evm _ imms (by simp))
  have hg := evalExpr_addressEq hs (evalStorage_guardian evm _ imms (by simp))
  have he := evalExpr_boolOr hg (evalExpr_boolOr hc ho)
  simpa [curatorGuardianCondition, curatorGuardianAllowed, guardianAddress, curatorAddress,
    ownerAddress, eq_comm] using he

theorem curatorGuardianPrefix (evm : EVM.State) (imms : Store) :
    ABlock config evm { contract := contract, locals := ∅, immutables := imms }
      curatorGuardianFunction.body (guardianRoleFrame evm imms)
      [.require curatorGuardianCondition] := by
  constructor
  intro result htail
  exact ExecBlock.consNormal
    (ExecStmt.letDecl (by simp [evalExpr?, envValue, pure])) htail

theorem curatorGuardianBodyReturns (evm : EVM.State) (imms : Store)
    (hrole : curatorGuardianAllowed evm) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms } evm
      curatorGuardianFunction.body (.returned (guardianRoleFrame evm imms) evm none) := by
  apply ExecFuncBody.execBlockOK
  apply ((curatorGuardianPrefix evm imms).requireStep (by
    simp only [curatorGuardianComparison, hrole, decide_true])).run
  exact ExecBlock.nil

theorem curatorGuardianBodyReverts (evm : EVM.State) (imms : Store)
    (hrole : ¬ curatorGuardianAllowed evm) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms } evm
      curatorGuardianFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact (curatorGuardianPrefix evm imms).requireRevert (by
    simp only [curatorGuardianComparison, hrole, decide_false])

theorem curatorGuardianCall (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (hrole : curatorGuardianAllowed evm) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkCuratorOrGuardianRole" [] retVar)
      (.ok { contract := contract, locals := locals.insert retVar .unit, immutables := imms }
        evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := curatorGuardianFunction) (value := none) rfl rfl rfl
    (curatorGuardianBodyReturns evm imms hrole)

theorem curatorGuardianCallReverts (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (hrole : ¬ curatorGuardianAllowed evm) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkCuratorOrGuardianRole" [] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := curatorGuardianFunction) rfl rfl rfl
    (curatorGuardianBodyReverts evm imms hrole)

end Benchmarks.Morpho.MetaMorphoV1_1
