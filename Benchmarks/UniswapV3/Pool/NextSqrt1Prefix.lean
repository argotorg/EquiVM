import Benchmarks.UniswapV3.Pool.NextSqrtModel
import Benchmarks.UniswapV3.Pool.WordShiftBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextSqrt1Branch (add : Bool) : List Stmt :=
  match (nextSqrtFunction true).body[0]! with
  | .ite _ yes no => if add then yes else no
  | _ => []

def nextSqrt1CondName (add : Bool) : String := if add then "__cond1" else "__cond6"

def nextSqrt1ZeroFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrtFrame imms a with
    locals := (nextSqrtLocals a).insert (nextSqrt1CondName a.add) (.int 0)}

theorem nextSqrt1ZeroSource (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    ExecStmt config (nextSqrtFrame imms a) evm (nextSqrt1Branch a.add)[0]!
      (.ok (nextSqrt1ZeroFrame imms a) evm) := by
  cases a with
  | mk price liquidity amount add =>
    cases add <;> exact ExecStmt.letDecl (by simp only [evalExpr?, pure])

theorem nextSqrt1ZeroGet (imms : Store) (a : NextSqrtArgs) :
    (nextSqrt1ZeroFrame imms a).locals.get? "sqrtPX96" = some (.int (Int.ofNat a.price.toNat)) ∧
      (nextSqrt1ZeroFrame imms a).locals.get? "liquidity" =
        some (.int (Int.ofNat a.liquidity.toNat)) ∧
      (nextSqrt1ZeroFrame imms a).locals.get? "amount" = some (.int (Int.ofNat a.amount.toNat)) ∧
      (nextSqrt1ZeroFrame imms a).locals.get? "add" = some (.bool a.add) ∧
      (nextSqrt1ZeroFrame imms a).locals.get? (nextSqrt1CondName a.add) = some (.int 0) := by
  obtain ⟨hp, hl, hm, ha⟩ := nextSqrtGet imms a
  cases h : a.add <;>
    simp only [nextSqrt1ZeroFrame, nextSqrt1CondName, h, Bool.false_eq_true,
      if_false, if_true, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;>
    exact ⟨hp, hl, hm, by simpa only [h] using ha, rfl⟩

def nextSqrt1SmallExpr : Expr :=
  .binary .le (.var "amount") (.intLit (2 ^ 160 - 1))

theorem evalNextSqrt1Small (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExpr? config (nextSqrt1ZeroFrame imms a) evm nextSqrt1SmallExpr =
      .ok (.bool (decide (nextSqrt1Small a))) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrt1ZeroGet imms a).2.2.1
  simp only [nextSqrt1SmallExpr, evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure]
  apply congrArg (fun b : Bool ↦ (EvalResult.ok (Value.bool b) : EvalResult Value))
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, nextSqrt1Small, Int.ofNat_eq_natCast]
  omega

def nextSqrt1ScaledExpr : Expr :=
  .binary (.shl (.uint ⟨256, by decide⟩)) (.var "amount") (.intLit 96)

theorem evalNextSqrt1Scaled (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExpr? config (nextSqrt1ZeroFrame imms a) evm nextSqrt1ScaledExpr =
      .ok (.int (Int.ofNat (nextSqrt1ScaledAmount a).toNat)) :=
  evalExpr_word_shl_by (evalExpr_var_get (nextSqrt1ZeroGet imms a).2.2.1)
    (by simp only [evalExpr?, pure]; rfl) (by decide)

def nextSqrt1FullArgs : List Expr :=
  [.var "amount", .intLit (2 ^ 96), .var "liquidity"]

theorem evalNextSqrt1FullArgs (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExprs? config (nextSqrt1ZeroFrame imms a) evm nextSqrt1FullArgs =
      .ok [.int (Int.ofNat a.amount.toNat), .int (Int.ofNat (UInt256.ofNat (2 ^ 96)).toNat),
        .int (Int.ofNat a.liquidity.toNat)] := by
  have ha := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrt1ZeroGet imms a).2.2.1
  have hl := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrt1ZeroGet imms a).2.1
  simp only [nextSqrt1FullArgs, evalExprs?, evalExpr?, ha, hl, bind, EvalResult.bind, pure]
  rfl

def nextSqrt1UnsafeArgs : List Expr := [nextSqrt1ScaledExpr, .var "liquidity"]

theorem evalNextSqrt1UnsafeArgs (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExprs? config (nextSqrt1ZeroFrame imms a) evm nextSqrt1UnsafeArgs =
      .ok [.int (Int.ofNat (nextSqrt1ScaledAmount a).toNat),
        .int (Int.ofNat a.liquidity.toNat)] := by
  have he := evalNextSqrt1Scaled imms evm a
  have hl := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrt1ZeroGet imms a).2.1
  simp only [nextSqrt1UnsafeArgs, evalExprs?, he, hl, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
