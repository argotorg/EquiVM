import Reasoning.Theory

/-!
# ActBody — compositional lemmas for the Act contract body

The Act-side analogue of the EVM trace: facts about `ExecContractBody` / `ExecStmt`.  The piece
shared across every solc contract is the **non-payable guard** `require(callvalue == 0)` that opens
each transition body — its evaluation (both directions) and the body-revert it produces under
non-zero call value.  Statement-level combinators for the success path / loops can be added here as
more contracts need them.
-/

open Act ABI Ethereum

namespace Reasoning.Theory

/-- The non-payable guard `callvalue == 0` evaluates to `true` when the call value is zero. -/
theorem evalCallvalueEq_true {cfg : Config} {act : Frame} {evm : EVM.State}
    (h : evm.executionEnv.weiValue = ⟨0⟩) :
    evalExpr? cfg act evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool true) := by
  have hval : (Value.int (Int.ofNat evm.executionEnv.weiValue.val) == Value.int 0) = true := by
    rw [h]; rfl
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-- The non-payable guard `callvalue == 0` evaluates to `false` when the call value is non-zero. -/
theorem evalCallvalueEq_false {cfg : Config} {act : Frame} {evm : EVM.State}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    evalExpr? cfg act evm (.binary .eq (.env .callvalue) (.intLit 0)) = .ok (.bool false) := by
  have hval : (Value.int (Int.ofNat evm.executionEnv.weiValue.val) == Value.int 0) = false := by
    rw [beq_eq_false_iff_ne]; intro hh; rw [Value.int.injEq] at hh
    exact h (uint256_toNat_eq_zero (Int.ofNat.inj hh))
  simp only [evalExpr?, EvalResult.bind, bind, pure, envValue, evalBinaryOp?, hval]

/-- **The non-payable guard reverts the body.**  Any transition whose body opens with
    `require(callvalue == 0)` reverts when the call value is non-zero — independent of the rest of
    the body.  Shared by every contract's `callvalue ≠ 0` case. -/
theorem bodyReverts_nonPayable {cfg : Config} {contract : ContractDecl} {evm : EVM.State}
    {locals : Store} {rest : List Stmt}
    (h : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecContractBody cfg contract evm locals
      (.require (.binary .eq (.env .callvalue) (.intLit 0)) :: rest) .reverted :=
  ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.requireFalse (evalCallvalueEq_false h)))

end Reasoning.Theory
