import Benchmarks.Morpho.MorphoBlue.AccruePublicSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev exactlyOneZeroFunction : FunctionDecl := contract.functions[2]!

def exactlyOneZero (x y : UInt256) : Bool := decide (x = ⟨0⟩) != decide (y = ⟨0⟩)

def exactlyOneZeroFrame (x y : UInt256) (imms : Store) : Frame :=
  { contract := contract, immutables := imms,
    locals := ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x" (.int (Int.ofNat x.toNat)) }

theorem morphoExactlyOneZeroBody (x y : UInt256) (evm : EVM.State) (imms : Store) :
    ExecFuncBody config (exactlyOneZeroFrame x y imms) evm exactlyOneZeroFunction.body
      (.returned (exactlyOneZeroFrame x y imms) evm (some [.bool (exactlyOneZero x y)])) := by
  have hx : evalExpr? config (exactlyOneZeroFrame x y imms) evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)) := by
    simp only [evalExpr?, exactlyOneZeroFrame, store_get_self, EvalResult.ofOption]
  have hy : evalExpr? config (exactlyOneZeroFrame x y imms) evm (.var "y") =
      .ok (.int (Int.ofNat y.toNat)) := by
    simp only [evalExpr?, exactlyOneZeroFrame, store_get_ne _ _ (show ("x" == "y") = false by decide),
      store_get_self, EvalResult.ofOption]
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  rw [evalExpr_binary_nonshort (by decide) (by decide), evalWordEqZero hx, evalWordEqZero hy]
  simp only [bind, EvalResult.bind, pure, evalBinaryOp?, exactlyOneZero]
  cases decide (x = ⟨0⟩) <;> cases decide (y = ⟨0⟩) <;> rfl

theorem morphoExactlyOneZeroCall (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (args : List Expr) (retVar : Ident)
    (he : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)]) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_exactlyOneZero" args retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.bool (exactlyOneZero x y)), immutables := imms } evm) :=
  internalCallFunctionReturn (callee := exactlyOneZeroFunction) (value := some [.bool (exactlyOneZero x y)])
    he rfl rfl (morphoExactlyOneZeroBody x y evm imms)

-- LIBRARY CANDIDATE: the optimizer implements exactly-one-zero by XOR of ISZERO results.
theorem exactlyOneZero_word (x y : UInt256) :
    UInt256.xor (UInt256.isZero x) (UInt256.isZero y) =
      if exactlyOneZero x y then UInt256.ofNat 1 else UInt256.ofNat 0 := by
  by_cases hx : x = ⟨0⟩ <;> by_cases hy : y = ⟨0⟩ <;>
    simp only [exactlyOneZero, hx, hy, ↓reduceIte, decide_true, decide_false]
  all_goals try rw [isZero_eq_zero_of_ne hx]
  all_goals try rw [isZero_eq_zero_of_ne hy]
  all_goals rfl

end Benchmarks.Morpho.MorphoBlue
