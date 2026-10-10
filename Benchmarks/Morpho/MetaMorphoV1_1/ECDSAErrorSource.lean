import Benchmarks.Morpho.MetaMorphoV1_1.ECDSATryReturn

/-! ECDSA's error handler returns exactly for the zero error code. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

def ecdsaThrowFunction : FunctionDecl := contract.functions[71]!

def ecdsaThrowFrame (imms : Store) (error errorArg : UInt256) : Frame :=
  ⟨contract, ((∅ : Store).insert "errorArg" (wordBytes32Value errorArg)).insert
    "error" (uint256Value error), imms⟩

theorem ecdsaErrorLt (evm : State) (imms : Store) (error errorArg : UInt256) (n : Nat) :
    evalExpr? config (ecdsaThrowFrame imms error errorArg) evm
      (.binary .lt (.var "error") (.intLit (Int.ofNat n))) =
      .ok (.bool (decide (error.toNat < n))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [evalExpr?, ecdsaThrowFrame, store_get_self, uint256Value, EvalResult.ofOption,
    bind, EvalResult.bind, pure, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]

theorem ecdsaErrorEq (evm : State) (imms : Store) (error errorArg : UInt256) (n : Nat) :
    evalExpr? config (ecdsaThrowFrame imms error errorArg) evm
      (.binary .eq (.var "error") (.intLit (Int.ofNat n))) =
      .ok (.bool (decide (error.toNat = n))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [evalExpr?, ecdsaThrowFrame, store_get_self, uint256Value, EvalResult.ofOption,
    bind, EvalResult.bind, pure]
  simp [evalBinaryOp?, BEq.beq]

theorem ecdsaErrorNe (evm : State) (imms : Store) (error errorArg : UInt256) (n : Nat) :
    evalExpr? config (ecdsaThrowFrame imms error errorArg) evm
      (.binary .ne (.var "error") (.intLit (Int.ofNat n))) =
      .ok (.bool (decide (error.toNat ≠ n))) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide)]
  simp only [evalExpr?, ecdsaThrowFrame, store_get_self, uint256Value, EvalResult.ofOption,
    bind, EvalResult.bind, pure]
  simp [evalBinaryOp?, BEq.beq]

theorem ecdsaThrowBodyReturns (evm : State) (imms : Store) (errorArg : UInt256) :
    ExecFuncBody config (ecdsaThrowFrame imms ⟨0⟩ errorArg) evm ecdsaThrowFunction.body
      (.returned (ecdsaThrowFrame imms ⟨0⟩ errorArg) evm (some [])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.requireTrue (by
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, decide_true] using
      ecdsaErrorLt evm imms ⟨0⟩ errorArg 4))
  apply ExecBlock.consReturn (ExecStmt.iteTrue (by
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, decide_true] using
      ecdsaErrorEq evm imms ⟨0⟩ errorArg 0) ?_)
  exact ExecBlock.consReturn (ExecStmt.return (by simp only [evalExprs?, pure]))

theorem ecdsaThrowBodyReverts (evm : State) (imms : Store) (error errorArg : UInt256)
    (hne : error ≠ ⟨0⟩) :
    ExecFuncBody config (ecdsaThrowFrame imms error errorArg) evm ecdsaThrowFunction.body
      .reverted := by
  have hn : error.toNat ≠ 0 := fun h ↦ hne (u256_inj h)
  apply ExecFuncBody.execBlockRevert
  by_cases hlt : error.toNat < 4
  · apply ExecBlock.consNormal (ExecStmt.requireTrue (by
      simpa only [hlt, decide_true] using ecdsaErrorLt evm imms error errorArg 4))
    apply ExecBlock.consRevert (ExecStmt.iteFalse (by
      simpa only [hn, decide_false] using ecdsaErrorEq evm imms error errorArg 0) ?_)
    by_cases h1 : error.toNat = 1
    · apply ExecBlock.consRevert (ExecStmt.iteTrue (by
        simpa only [h1, decide_true] using ecdsaErrorEq evm imms error errorArg 1) ?_)
      exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))
    · apply ExecBlock.consRevert (ExecStmt.iteFalse (by
        simpa only [h1, decide_false] using ecdsaErrorEq evm imms error errorArg 1) ?_)
      by_cases h2 : error.toNat = 2
      · apply ExecBlock.consRevert (ExecStmt.iteTrue (by
          simpa only [h2, decide_true] using ecdsaErrorEq evm imms error errorArg 2) ?_)
        exact ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))
      · apply ExecBlock.consRevert (ExecStmt.iteFalse (by
          simpa only [h2, decide_false] using ecdsaErrorEq evm imms error errorArg 2) ?_)
        have h3 : error.toNat = 3 := by omega
        exact ExecBlock.consRevert (ExecStmt.requireFalse (by
          simpa only [h3, ne_eq, not_true_eq_false, decide_false] using
            ecdsaErrorNe evm imms error errorArg 3))
  · exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [hlt, decide_false] using ecdsaErrorLt evm imms error errorArg 4))

theorem ecdsaThrowCall {evm : State} {locals imms : Store}
    {errorArg : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [uint256Value ⟨0⟩, wordBytes32Value errorArg]) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "ECDSA__throwError" args ret)
      (.ok ⟨contract, locals.insert ret .unit, imms⟩ evm) :=
  internalCallFunctionReturn (callee := ecdsaThrowFunction) hargs rfl rfl
    (ecdsaThrowBodyReturns evm imms errorArg)

theorem ecdsaThrowCallReverts {evm : State} {locals imms : Store}
    {error errorArg : UInt256} {args : List Expr} {ret : Ident}
    (hargs : evalExprs? config ⟨contract, locals, imms⟩ evm args =
      .ok [uint256Value error, wordBytes32Value errorArg]) (hne : error ≠ ⟨0⟩) :
    ExecStmt config ⟨contract, locals, imms⟩ evm (.internalCall "ECDSA__throwError" args ret)
      .reverted :=
  ExecStmt.internalCallRevert (callee := ecdsaThrowFunction.toCallable) hargs rfl rfl
    (ecdsaThrowBodyReverts evm imms error errorArg hne)

end Benchmarks.Morpho.MetaMorphoV1_1
