import Benchmarks.UniswapV3.Pool.SourceSignedBits
import Benchmarks.UniswapV3.Pool.SourceExpressions

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000
attribute [local instance] Classical.propDecidable

def safeSignedMathResult (subtract : Bool) (x y : Int) : Int :=
  normalizeInt (.sint ⟨256, by decide⟩) (if subtract then x - y else x + y)

def safeSignedMathValid (subtract : Bool) (x y : Int) : Prop :=
  (if subtract then safeSignedMathResult subtract x y ≤ x
    else x ≤ safeSignedMathResult subtract x y) ↔ 0 ≤ y

def safeSignedMathFunction (subtract : Bool) : FunctionDecl :=
  if subtract then contract.functions[20]! else contract.functions[21]!

theorem safeSignedMathLookup (subtract : Bool) :
    lookupCallable? contract
      (if subtract then "LowGasSafeMath_sub" else "LowGasSafeMath_add_int256_int256") =
      some (safeSignedMathFunction subtract).toCallable := by cases subtract <;> rfl

def safeSignedMathLocals (x y : Int) : Store :=
  ((∅ : Store).insert "y" (.int y)).insert "x" (.int x)

def safeSignedMathFrame (imms : Store) (x y : Int) : Frame :=
  {contract := contract, locals := safeSignedMathLocals x y, immutables := imms}

def safeSignedMathZeroFrame (imms : Store) (x y : Int) : Frame :=
  {safeSignedMathFrame imms x y with locals := (safeSignedMathLocals x y).insert "z" (.int 0)}

def safeSignedMathReadyFrame (subtract : Bool) (imms : Store) (x y : Int) : Frame :=
  {safeSignedMathZeroFrame imms x y with
    locals := (safeSignedMathZeroFrame imms x y).locals.insert "z"
      (.int (safeSignedMathResult subtract x y))}

theorem safeSignedMathBind (subtract : Bool) (x y : Int) :
    bindParams? (safeSignedMathFunction subtract).params [.int x, .int y] =
      some (safeSignedMathLocals x y) := by cases subtract <;> rfl

def safeSignedMathResultExpr (subtract : Bool) : Expr :=
  .cast (.binary (if subtract then .sub else .add) (.var "x") (.var "y"))
    (.elem (.int (.sint ⟨256, by decide⟩)))

def safeSignedMathGuardExpr (subtract : Bool) : Expr :=
  .binary .eq (.binary (if subtract then .le else .ge) (.var "z") (.var "x"))
    (.binary .ge (.var "y") (.intLit 0))

theorem safeSignedMathBody (subtract : Bool) :
    (safeSignedMathFunction subtract).body =
      [.letDecl "z" (some (.elem (.int (.sint ⟨256, by decide⟩)))) (.intLit 0),
       .assign .localVar ⟨"z", []⟩ (safeSignedMathResultExpr subtract),
       .require (safeSignedMathGuardExpr subtract), .return [.var "z"]] := by
  cases subtract <;> rfl

theorem safeSignedMathReadySource (subtract : Bool) (imms : Store) (evm : EVM.State)
    (x y : Int) :
    ExecBlock config (safeSignedMathFrame imms x y) evm
      ((safeSignedMathFunction subtract).body.take 2)
      (.ok (safeSignedMathReadyFrame subtract imms x y) evm) := by
  rw [safeSignedMathBody]
  refine ExecBlock.consNormal (solm' := safeSignedMathZeroFrame imms x y)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.assign
    (value := .int (safeSignedMathResult subtract x y)) ?_
    (assignLocalVarBase_frame Std.HashMap.getElem?_insert_self)) ExecBlock.nil
  have hx : (safeSignedMathZeroFrame imms x y).locals.get? "x" = some (.int x) := by
    simp only [safeSignedMathZeroFrame, safeSignedMathLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hy : (safeSignedMathZeroFrame imms x y).locals.get? "y" = some (.int y) := by
    simp only [safeSignedMathZeroFrame, safeSignedMathLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hex := evalExpr_var_get (cfg := config) (evm := evm) hx
  have hey := evalExpr_var_get (cfg := config) (evm := evm) hy
  cases subtract <;> simp only [safeSignedMathResultExpr, safeSignedMathResult,
    Bool.false_eq_true, ↓reduceIte, evalExpr?, hex, hey, evalBinaryOp?, castValue?,
    EvalResult.ofOption, bind, EvalResult.bind]

theorem evalSafeSignedMathGuard (subtract : Bool) (imms : Store) (evm : EVM.State)
    (x y : Int) :
    evalExpr? config (safeSignedMathReadyFrame subtract imms x y) evm
      (safeSignedMathGuardExpr subtract) =
      .ok (.bool (decide (safeSignedMathValid subtract x y))) := by
  have hx : (safeSignedMathReadyFrame subtract imms x y).locals.get? "x" =
      some (.int x) := by
    simp only [safeSignedMathReadyFrame, safeSignedMathZeroFrame, safeSignedMathLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hy : (safeSignedMathReadyFrame subtract imms x y).locals.get? "y" =
      some (.int y) := by
    simp only [safeSignedMathReadyFrame, safeSignedMathZeroFrame, safeSignedMathLocals,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hex := evalExpr_var_get (cfg := config) (evm := evm) hx
  have hey := evalExpr_var_get (cfg := config) (evm := evm) hy
  have hez : evalExpr? config (safeSignedMathReadyFrame subtract imms x y) evm (.var "z") =
      .ok (.int (safeSignedMathResult subtract x y)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  cases subtract
  · by_cases hc : x ≤ safeSignedMathResult false x y <;> by_cases hy0 : 0 ≤ y
    all_goals simp only [safeSignedMathGuardExpr, safeSignedMathValid, Bool.false_eq_true,
      ↓reduceIte, evalExpr?, hex, hey, hez, evalBinaryOp?, bind, EvalResult.bind, pure,
      hc, hy0, decide_true, decide_false, iff_self, true_iff, false_iff, not_true_eq_false,
      not_false_eq_true]
    all_goals rfl
  · by_cases hc : safeSignedMathResult true x y ≤ x <;> by_cases hy0 : 0 ≤ y
    all_goals simp only [safeSignedMathGuardExpr, safeSignedMathValid, ↓reduceIte,
      evalExpr?, hex, hey, hez, evalBinaryOp?, bind, EvalResult.bind, pure,
      hc, hy0, decide_true, decide_false, iff_self, true_iff, false_iff, not_true_eq_false,
      not_false_eq_true]
    all_goals rfl

theorem safeSignedMathReturns (subtract : Bool) (imms : Store) (evm : EVM.State)
    (x y : Int) (hv : safeSignedMathValid subtract x y) :
    ExecFuncBody config (safeSignedMathFrame imms x y) evm
      (safeSignedMathFunction subtract).body
      (.returned (safeSignedMathReadyFrame subtract imms x y) evm
        (some [.int (safeSignedMathResult subtract x y)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 2 (safeSignedMathFunction subtract).body]
  apply execBlock_append_ok (safeSignedMathReadySource subtract imms evm x y)
  rw [safeSignedMathBody]
  refine ExecBlock.consNormal (ExecStmt.requireTrue
    (by simpa only [hv, decide_true] using evalSafeSignedMathGuard subtract imms evm x y)) ?_
  refine ExecBlock.consReturn (ExecStmt.return ?_)
  have he : evalExpr? config (safeSignedMathReadyFrame subtract imms x y) evm (.var "z") =
      .ok (.int (safeSignedMathResult subtract x y)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem safeSignedMathReverts (subtract : Bool) (imms : Store) (evm : EVM.State)
    (x y : Int) (hv : ¬ safeSignedMathValid subtract x y) :
    ExecFuncBody config (safeSignedMathFrame imms x y) evm
      (safeSignedMathFunction subtract).body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 (safeSignedMathFunction subtract).body]
  apply execBlock_append_ok (safeSignedMathReadySource subtract imms evm x y)
  rw [safeSignedMathBody]
  exact ExecBlock.consRevert (ExecStmt.requireFalse
    (by simpa only [hv, decide_false] using evalSafeSignedMathGuard subtract imms evm x y))

theorem safeSignedMathValid_iff (subtract : Bool) (x y : Int)
    (hxlo : -(2 ^ 255 : Int) ≤ x) (hxhi : x < 2 ^ 255)
    (hylo : -(2 ^ 255 : Int) ≤ y) (hyhi : y < 2 ^ 255) :
    safeSignedMathValid subtract x y ↔
      -(2 ^ 255 : Int) ≤ (if subtract then x - y else x + y) ∧
        (if subtract then x - y else x + y) < 2 ^ 255 := by
  cases subtract <;> unfold safeSignedMathValid safeSignedMathResult
  all_goals norm_num only [Bool.false_eq_true, ↓reduceIte, normalizeInt, EVM.twoPow]
  all_goals split <;> omega

end Benchmarks.UniswapV3.Pool
