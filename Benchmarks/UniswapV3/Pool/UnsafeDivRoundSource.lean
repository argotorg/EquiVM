import Benchmarks.UniswapV3.Pool.SourceWordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def unsafeDivRoundNat (x y : UInt256) : Nat :=
  if y.toNat = 0 then 0 else x.toNat / y.toNat + if x.toNat % y.toNat = 0 then 0 else 1

theorem unsafeDivRoundNat_le (x y : UInt256) : unsafeDivRoundNat x y ≤ x.toNat := by
  unfold unsafeDivRoundNat
  split_ifs with hy hr
  · omega
  · simpa only [Nat.add_zero] using Nat.div_le_self x.toNat y.toNat
  · have hx : 0 < x.toNat := by
      by_contra h
      have hz : x.toNat = 0 := by omega
      exact hr (by rw [hz, Nat.zero_mod])
    have hy2 : 1 < y.toNat := by
      by_contra h
      have hone : y.toNat = 1 := by omega
      exact hr (by rw [hone, Nat.mod_one])
    have hd := Nat.div_lt_self hx hy2
    omega

def unsafeDivRoundResult (x y : UInt256) : UInt256 := UInt256.ofNat (unsafeDivRoundNat x y)

theorem unsafeDivRoundResult_toNat (x y : UInt256) :
    (unsafeDivRoundResult x y).toNat = unsafeDivRoundNat x y :=
  UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (unsafeDivRoundNat_le x y) x.val.isLt)

def unsafeDivRoundFunction : FunctionDecl := contract.functions[47]!

theorem unsafeDivRoundLookup : lookupCallable? contract "UnsafeMath_divRoundingUp" =
    some unsafeDivRoundFunction.toCallable := rfl

def unsafeDivRoundLocals (x y : UInt256) : Store :=
  ((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert "x" (.int (Int.ofNat x.toNat))

def unsafeDivRoundFrame (imms : Store) (x y : UInt256) : Frame :=
  {contract := contract, locals := unsafeDivRoundLocals x y, immutables := imms}

theorem unsafeDivRoundBind (x y : UInt256) : bindParams? unsafeDivRoundFunction.params
    [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] = some (unsafeDivRoundLocals x y) := rfl

def unsafeDivRoundExpr : Expr :=
  .binary .add (.binary .div (.var "x") (.var "y"))
    (.ite (.binary .eq (.binary .mod (.var "x") (.var "y")) (.intLit 0)) (.intLit 0) (.intLit 1))

theorem evalUnsafeDivRoundExpr (imms : Store) (evm : EVM.State) (x y : UInt256)
    (hn : y.toNat ≠ 0) :
    evalExpr? config (unsafeDivRoundFrame imms x y) evm unsafeDivRoundExpr =
      .ok (.int (Int.ofNat (unsafeDivRoundNat x y))) := by
  have hx : evalExpr? config (unsafeDivRoundFrame imms x y) evm (.var "x") =
      .ok (.int (Int.ofNat x.toNat)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
  have hy : evalExpr? config (unsafeDivRoundFrame imms x y) evm (.var "y") =
      .ok (.int (Int.ofNat y.toNat)) := evalExpr_var_get (by
        simp only [unsafeDivRoundFrame, unsafeDivRoundLocals, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
  have hd := evalExpr_word_div hx hy hn
  have hr := evalExpr_nat_eq_zero (evalExpr_word_mod hx hy hn)
  rw [umod_toNat_of_ne_zero x y hn] at hr
  rw [udiv_toNat] at hd
  by_cases hz : x.toNat % y.toNat = 0
  all_goals
    simp only [unsafeDivRoundExpr, unsafeDivRoundNat, if_neg hn, evalExpr?, hd, hr,
      hz, decide_true, decide_false, if_true, if_false, bind, EvalResult.bind, pure,
      evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_zero, Nat.cast_one]

theorem unsafeDivRoundReturns (imms : Store) (evm : EVM.State) (x y : UInt256) :
    ExecFuncBody config (unsafeDivRoundFrame imms x y) evm unsafeDivRoundFunction.body
      (.returned (unsafeDivRoundFrame imms x y) evm
        (some [.int (Int.ofNat (unsafeDivRoundResult x y).toNat)])) := by
  rw [unsafeDivRoundResult_toNat]
  have hy : evalExpr? config (unsafeDivRoundFrame imms x y) evm (.var "y") =
      .ok (.int (Int.ofNat y.toNat)) := evalExpr_var_get (by
        simp only [unsafeDivRoundFrame, unsafeDivRoundLocals, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert]; rfl)
  have hg := evalExpr_nat_eq_zero hy
  apply ExecFuncBody.execBlockRet
  by_cases hz : y.toNat = 0
  · simp only [unsafeDivRoundNat, if_pos hz]
    apply ExecBlock.consReturn (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hg) ?_)
    exact ExecBlock.consReturn (ExecStmt.return
      (by simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure]; rfl))
  · refine ExecBlock.consNormal (ExecStmt.iteFalse
      (by simpa only [decide_eq_false hz] using hg) ExecBlock.nil) ?_
    apply ExecBlock.consReturn (ExecStmt.return ?_)
    have he := evalUnsafeDivRoundExpr imms evm x y hz
    change evalExprs? config (unsafeDivRoundFrame imms x y) evm [unsafeDivRoundExpr] = _
    simp only [evalExprs?, he, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
