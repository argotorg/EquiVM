import Benchmarks.Morpho.MetaMorphoV1_1.AccessControl

/-! The owner-or-guardian authorization shared by pending-change revocations. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

def guardianAddress (evm : EVM.State) : AccountAddress :=
  AccountAddress.ofNat (UInt256.land
    (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩) solcAddrMask).toNat

abbrev guardianRoleAllowed (evm : EVM.State) : Prop :=
  ownerAddress evm = evm.executionEnv.source ∨ guardianAddress evm = evm.executionEnv.source

abbrev checkGuardianRoleFunction : FunctionDecl := contract.functions[10]!

def guardianRoleFrame (evm : EVM.State) (imms : Store) : Frame :=
  { contract := contract
    locals := (∅ : Store).insert "sender" (.address evm.executionEnv.source)
    immutables := imms }

def guardianRoleCondition : Expr :=
  .binary .or (.binary .eq (.var "sender") (.storage ⟨"_owner", []⟩))
    (.binary .eq (.var "sender") (.storage ⟨"guardian", []⟩))

theorem guardianRoleComparison (evm : EVM.State) (imms : Store) :
    evalExpr? config (guardianRoleFrame evm imms) evm guardianRoleCondition =
      .ok (.bool (decide (guardianRoleAllowed evm))) := by
  have hs : evalExpr? config (guardianRoleFrame evm imms) evm (.var "sender") =
      .ok (.address evm.executionEnv.source) := by
    simp [evalExpr?, guardianRoleFrame, EvalResult.ofOption]
  have ho := evalExpr_addressEq hs (evalStorage_owner evm _ imms (by simp))
  have hg := evalExpr_addressEq hs (evalStorage_guardian evm _ imms (by simp))
  change evalExpr? config (guardianRoleFrame evm imms) evm
    (.binary .eq (.var "sender") (.storage ⟨"_owner", []⟩)) =
      .ok (.bool (decide (evm.executionEnv.source = ownerAddress evm))) at ho
  change evalExpr? config (guardianRoleFrame evm imms) evm
    (.binary .eq (.var "sender") (.storage ⟨"guardian", []⟩)) =
      .ok (.bool (decide (evm.executionEnv.source = guardianAddress evm))) at hg
  unfold guardianRoleCondition
  rw [evalExpr?]
  simp only [ho, bind, EvalResult.bind]
  by_cases howner : ownerAddress evm = evm.executionEnv.source
  · simp [howner, guardianRoleAllowed, pure]
  · simp [howner, Ne.symm howner, hg, guardianRoleAllowed, bind, EvalResult.bind, pure,
      eq_comm]

theorem guardianRolePrefix (evm : EVM.State) (imms : Store) :
    ABlock config evm { contract := contract, locals := ∅, immutables := imms }
      checkGuardianRoleFunction.body (guardianRoleFrame evm imms)
      [.require guardianRoleCondition] := by
  constructor
  intro result htail
  exact ExecBlock.consNormal (ExecStmt.letDecl
    (by simp [evalExpr?, envValue, pure])) htail

theorem guardianRoleBodyReturns (evm : EVM.State) (imms : Store)
    (hrole : guardianRoleAllowed evm) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms } evm
      checkGuardianRoleFunction.body (.returned (guardianRoleFrame evm imms) evm none) := by
  apply ExecFuncBody.execBlockOK
  apply ((guardianRolePrefix evm imms).requireStep (by
    simp only [guardianRoleComparison, hrole, decide_true])).run
  exact ExecBlock.nil

theorem guardianRoleBodyReverts (evm : EVM.State) (imms : Store)
    (hrole : ¬ guardianRoleAllowed evm) :
    ExecFuncBody config { contract := contract, locals := ∅, immutables := imms } evm
      checkGuardianRoleFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact (guardianRolePrefix evm imms).requireRevert (by
    simp only [guardianRoleComparison, hrole, decide_false])

theorem guardianRoleCall (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (hrole : guardianRoleAllowed evm) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkGuardianRole" [] retVar)
      (.ok { contract := contract, locals := locals.insert retVar .unit, immutables := imms }
        evm) := by
  exact internalCallFunctionReturn
    (caller := { contract := contract, locals := locals, immutables := imms })
    (callee := checkGuardianRoleFunction) (value := none) rfl rfl rfl
    (guardianRoleBodyReturns evm imms hrole)

theorem guardianRoleCallReverts (evm : EVM.State) (locals imms : Store) (retVar : Ident)
    (hrole : ¬ guardianRoleAllowed evm) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "_checkGuardianRole" [] retVar) .reverted := by
  exact internalCallFunctionRevert (callee := checkGuardianRoleFunction) rfl rfl rfl
    (guardianRoleBodyReverts evm imms hrole)

end Benchmarks.Morpho.MetaMorphoV1_1
