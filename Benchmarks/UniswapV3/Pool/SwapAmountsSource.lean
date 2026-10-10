import Benchmarks.UniswapV3.Pool.SwapMemoryModel
import Benchmarks.UniswapV3.Pool.SourceSignedBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapAmountDifference (a : SwapArgs) (s : SwapStateData) : Int :=
  normalizeInt (.sint ⟨256, by decide⟩) (a.amountSpecified - s.remaining)

def swapAmount0 (a : SwapArgs) (s : SwapStateData) : Int :=
  if a.zeroForOne = swapExactInput a then swapAmountDifference a s else s.calculated

def swapAmount1 (a : SwapArgs) (s : SwapStateData) : Int :=
  if a.zeroForOne = swapExactInput a then s.calculated else swapAmountDifference a s

def swapAmountsFirstFrame (frame : Frame) (a : SwapArgs) (s : SwapStateData) : Frame :=
  {frame with locals := frame.locals.insert "amount0" (.int (swapAmount0 a s))}

def swapAmountsFrame (frame : Frame) (a : SwapArgs) (s : SwapStateData) : Frame :=
  {frame with
    locals := (frame.locals.insert "amount0" (.int (swapAmount0 a s))).insert
      "amount1" (.int (swapAmount1 a s))}

def swapAmountDifferenceExpr : Expr :=
  .cast (.binary .sub (.var "amountSpecified") (.field (.var "state") "amountSpecifiedRemaining"))
    (.elem (.int (.sint ⟨256, by decide⟩)))

theorem swapAmountDifference_word (a : SwapArgs) (s : SwapStateData) :
    EVM.wordOfInt (swapAmountDifference a s) =
      UInt256.sub (EVM.wordOfInt a.amountSpecified) (EVM.wordOfInt s.remaining) := by
  rw [swapAmountDifference, wordOfInt_normalize256, wordOfInt_sub]

theorem swapAmounts_bounds (a : SwapArgs) (s : SwapStateData) (hs : s.Fits) :
    (-(2 ^ 255 : Int) ≤ swapAmount0 a s ∧ swapAmount0 a s < 2 ^ 255) ∧
    (-(2 ^ 255 : Int) ≤ swapAmount1 a s ∧ swapAmount1 a s < 2 ^ 255) := by
  have hd := normalizeSint_bounds ⟨256, by decide⟩ (a.amountSpecified - s.remaining)
  by_cases h : a.zeroForOne = swapExactInput a
  · exact ⟨by simpa only [swapAmount0, h, if_true, swapAmountDifference] using hd,
      by simpa only [swapAmount1, h, if_true] using hs.2.1⟩
  · exact ⟨by simpa only [swapAmount0, h, if_false] using hs.2.1,
      by simpa only [swapAmount1, h, if_false, swapAmountDifference] using hd⟩

theorem swapAmountsFrame_parts (frame : Frame) (a : SwapArgs) (s : SwapStateData) :
    (swapAmountsFrame frame a s).contract = frame.contract ∧
    (swapAmountsFrame frame a s).immutables = frame.immutables := ⟨rfl, rfl⟩

theorem swapAmountsFrame_get (frame : Frame) (a : SwapArgs) (s : SwapStateData) (name : Ident)
    (hn0 : name ≠ "amount0") (hn1 : name ≠ "amount1") :
    (swapAmountsFrame frame a s).locals.get? name = frame.locals.get? name := by
  simp only [swapAmountsFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    beq_iff_eq, Ne.symm hn0, Ne.symm hn1, if_false]

theorem swapAmountsFrame_amount0 (frame : Frame) (a : SwapArgs) (s : SwapStateData) :
    (swapAmountsFrame frame a s).locals.get? "amount0" = some (.int (swapAmount0 a s)) := by
  simp only [swapAmountsFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl

theorem swapAmountsFrame_amount1 (frame : Frame) (a : SwapArgs) (s : SwapStateData) :
    (swapAmountsFrame frame a s).locals.get? "amount1" = some (.int (swapAmount1 a s)) :=
  Std.HashMap.getElem?_insert_self

-- LIBRARY CANDIDATE: equality of Boolean expressions in arbitrary source frames.
theorem evalExpr_bool_eq {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Bool}
    (ha : evalExpr? cfg frame evm lhs = .ok (.bool a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.bool b)) :
    evalExpr? cfg frame evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  cases a <;> cases b <;> rfl

theorem evalSwapAmountDifference {frame : Frame} {evm : EVM.State}
    (a : SwapArgs) (s : SwapStateData)
    (ha : frame.locals.get? "amountSpecified" = some (.int a.amountSpecified))
    (hs : frame.locals.get? "state" = some s.value) :
    evalExpr? config frame evm swapAmountDifferenceExpr = .ok (.int (swapAmountDifference a s)) :=
      by
  have he : evalExpr? config frame evm (.field (.var "state") "amountSpecifiedRemaining") =
      .ok (.int s.remaining) :=
    evalExpr_structField (name := "amountSpecifiedRemaining") (evalExpr_var_get hs) rfl
  have hv := evalExpr_var_get (cfg := config) (evm := evm) ha
  simp only [swapAmountDifferenceExpr, swapAmountDifference, evalExpr?, hv, he,
    bind, EvalResult.bind, evalBinaryOp?, castValue?, EvalResult.ofOption]

theorem swapAmountsSource {frame : Frame} {evm : EVM.State} {old0 old1 : Value}
    (a : SwapArgs) (s : SwapStateData)
    (hz : frame.locals.get? "zeroForOne" = some (.bool a.zeroForOne))
    (he : frame.locals.get? "exactInput" = some (.bool (swapExactInput a)))
    (ha : frame.locals.get? "amountSpecified" = some (.int a.amountSpecified))
    (hs : frame.locals.get? "state" = some s.value)
    (h0 : frame.locals.get? "amount0" = some old0)
    (h1 : frame.locals.get? "amount1" = some old1) :
    ExecStmt config frame evm swapTransition.body[17]! (.ok (swapAmountsFrame frame a s) evm) := by
  have hguard := evalExpr_bool_eq
    (evalExpr_var_get (cfg := config) (evm := evm) hz) (evalExpr_var_get he)
  have hd := evalSwapAmountDifference (evm := evm) a s ha hs
  have hc : evalExpr? config frame evm (.field (.var "state") "amountCalculated") =
      .ok (.int s.calculated) :=
    evalExpr_structField (name := "amountCalculated") (evalExpr_var_get hs) rfl
  have hget (name : Ident) (hn : name ≠ "amount0") :
      (swapAmountsFirstFrame frame a s).locals.get? name = frame.locals.get? name := by
    simp only [swapAmountsFirstFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, Ne.symm hn, if_false]
  have hd1 := evalSwapAmountDifference (evm := evm) a s
    ((hget "amountSpecified" (by decide)).trans ha) ((hget "state" (by decide)).trans hs)
  have hc1 : evalExpr? config (swapAmountsFirstFrame frame a s) evm
      (.field (.var "state") "amountCalculated") = .ok (.int s.calculated) :=
    evalExpr_structField (name := "amountCalculated")
      (evalExpr_var_get ((hget "state" (by decide)).trans hs)) rfl
  have has0 := assignLocalVarBase_frame (cfg := config) (evm := evm)
    (value := .int (swapAmount0 a s)) h0
  have has1 := assignLocalVarBase_frame (cfg := config) (evm := evm)
    (value := .int (swapAmount1 a s)) ((hget "amount1" (by decide)).trans h1)
  by_cases h : a.zeroForOne = swapExactInput a
  · rw [show decide (a.zeroForOne = swapExactInput a) = true from decide_eq_true h] at hguard
    apply ExecStmt.iteTrue hguard
    exact ExecBlock.consNormal
      (ExecStmt.assign (by simpa only [swapAmount0, h, if_true] using hd) has0)
      (ExecBlock.consNormal
        (ExecStmt.assign (by simpa only [swapAmount1, h, if_true] using hc1) has1) .nil)
  · rw [show decide (a.zeroForOne = swapExactInput a) = false from decide_eq_false h] at hguard
    apply ExecStmt.iteFalse hguard
    exact ExecBlock.consNormal
      (ExecStmt.assign (by simpa only [swapAmount0, h, if_false] using hc) has0)
      (ExecBlock.consNormal
        (ExecStmt.assign (by simpa only [swapAmount1, h, if_false] using hd1) has1) .nil)

end Benchmarks.UniswapV3.Pool
