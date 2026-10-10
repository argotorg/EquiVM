import Benchmarks.UniswapV3.Pool.NextSqrt0Model

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextSqrt0Branch (add : Bool) : List Stmt :=
  match (nextSqrtFunction false).body[2]! with
  | .ite _ yes no => if add then yes else no
  | _ => []

def nextSqrt0NumeratorFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrtFrame imms a with
    locals := (nextSqrtLocals a).insert "numerator1"
      (.int (Int.ofNat (nextSqrt0Numerator a).toNat))}

def nextSqrt0ProductZeroFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt0NumeratorFrame imms a with
    locals := (nextSqrt0NumeratorFrame imms a).locals.insert "product" (.int 0)}

def nextSqrt0ProductFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt0ProductZeroFrame imms a with
    locals := (nextSqrt0ProductZeroFrame imms a).locals.insert "product"
      (.int (Int.ofNat (nextSqrt0Product a).toNat))}

theorem evalNextSqrt0Zero (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExpr? config (nextSqrtFrame imms a) evm (.binary .eq (.var "amount") (.intLit 0)) =
      .ok (.bool (decide (a.amount.toNat = 0))) :=
  evalExpr_nat_eq_zero (evalExpr_var_get (nextSqrtGet imms a).2.2.1)

theorem nextSqrt0ZeroReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hz : a.amount.toNat = 0) :
    ExecFuncBody config (nextSqrtFrame imms a) evm (nextSqrtFunction false).body
      (.returned (nextSqrtFrame imms a) evm (some [.int (Int.ofNat a.price.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn (ExecStmt.iteTrue ?_ ?_)
  · simpa only [hz, decide_true] using evalNextSqrt0Zero imms evm a
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have hp := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrtGet imms a).1
  simp only [evalExprs?, hp, bind, EvalResult.bind, pure]

theorem nextSqrt0NumeratorSource (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hn : a.amount.toNat ≠ 0) :
    ExecBlock config (nextSqrtFrame imms a) evm ((nextSqrtFunction false).body.take 2)
      (.ok (nextSqrt0NumeratorFrame imms a) evm) := by
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil)
    (ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil)
  · simpa only [hn, decide_false] using evalNextSqrt0Zero imms evm a
  · have hl := evalExpr_intCast (.uint ⟨256, by decide⟩)
      (evalExpr_var_get (cfg := config) (evm := evm) (nextSqrtGet imms a).2.1)
    rw [normalizeInt_uint256_word] at hl
    exact evalExpr_word_shl_by hl (by simp only [evalExpr?, pure]; rfl) (by decide)

macro "next_sqrt_0_product_get" : tactic =>
  `(tactic| simp only [nextSqrt0ProductFrame, nextSqrt0ProductZeroFrame,
    nextSqrt0NumeratorFrame, nextSqrtFrame, nextSqrtLocals,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert])

theorem nextSqrt0ProductSource (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    ExecBlock config (nextSqrt0NumeratorFrame imms a) evm ((nextSqrt0Branch a.add).take 2)
      (.ok (nextSqrt0ProductFrame imms a) evm) := by
  have hp : evalExpr? config (nextSqrt0ProductZeroFrame imms a) evm (.var "sqrtPX96") =
      .ok (.int (Int.ofNat a.price.toNat)) :=
    evalExpr_var_get (by next_sqrt_0_product_get; rfl)
  have hm : evalExpr? config (nextSqrt0ProductZeroFrame imms a) evm (.var "amount") =
      .ok (.int (Int.ofNat a.amount.toNat)) :=
    evalExpr_var_get (by next_sqrt_0_product_get; rfl)
  cases ha : a.add
  all_goals
    exact ExecBlock.consNormal (solm' := nextSqrt0ProductZeroFrame imms a)
      (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
      (ExecBlock.consNormal (ExecStmt.assign (evalExpr_word_mul hm hp)
        (assignLocalVarBase_frame Std.HashMap.getElem?_insert_self)) ExecBlock.nil)

theorem nextSqrt0ProductGet (imms : Store) (a : NextSqrtArgs) :
    (nextSqrt0ProductFrame imms a).locals.get? "sqrtPX96" =
        some (.int (Int.ofNat a.price.toNat)) ∧
      (nextSqrt0ProductFrame imms a).locals.get? "amount" =
        some (.int (Int.ofNat a.amount.toNat)) ∧
      (nextSqrt0ProductFrame imms a).locals.get? "add" = some (.bool a.add) ∧
      (nextSqrt0ProductFrame imms a).locals.get? "numerator1" =
        some (.int (Int.ofNat (nextSqrt0Numerator a).toNat)) ∧
      (nextSqrt0ProductFrame imms a).locals.get? "product" =
        some (.int (Int.ofNat (nextSqrt0Product a).toNat)) := by
  next_sqrt_0_product_get
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

def nextSqrt0ProductGuardExpr : Expr :=
  .binary .eq (.binary .div (.var "product") (.var "amount")) (.var "sqrtPX96")

theorem evalNextSqrt0ProductGuard (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hn : a.amount.toNat ≠ 0) :
    evalExpr? config (nextSqrt0ProductFrame imms a) evm nextSqrt0ProductGuardExpr =
      .ok (.bool (decide (nextSqrt0ProductExact a))) :=
  evalExpr_word_eq (evalExpr_word_div
    (evalExpr_var_get (nextSqrt0ProductGet imms a).2.2.2.2)
    (evalExpr_var_get (nextSqrt0ProductGet imms a).2.1) hn)
    (evalExpr_var_get (nextSqrt0ProductGet imms a).1)

end Benchmarks.UniswapV3.Pool
