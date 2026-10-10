import Benchmarks.UniswapV3.Pool.TickSqrtPrefix
import Benchmarks.UniswapV3.Pool.SourceWordBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickSqrtInvertedFrame (frame : Frame) (tick : Int) (ratio : UInt256) : Frame :=
  if 0 < tick then
    {frame with locals := frame.locals.insert "ratio" (.int (Int.ofNat (tickSqrtInvert tick ratio).toNat))}
  else frame

theorem tickSqrtInvertSource {frame : Frame} {evm : EVM.State} (tick : Int) (ratio : UInt256)
    (ht : frame.locals.get? "tick" = some (.int tick))
    (hr : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat)))
    (hn : 0 < ratio.toNat) :
    ExecStmt config frame evm tickSqrtFunction.body[23]!
      (.ok (tickSqrtInvertedFrame frame tick ratio) evm) := by
  have hgt : evalExpr? config frame evm (.binary .gt (.var "tick") (.intLit 0)) =
      .ok (.bool (decide (0 < tick))) := by
    simp only [evalExpr?, ht, EvalResult.ofOption, bind, EvalResult.bind, pure, evalBinaryOp?]
  by_cases hp : 0 < tick
  · rw [tickSqrtInvertedFrame, if_pos hp]
    refine ExecStmt.iteTrue ?_ (ExecBlock.consNormal
      (ExecStmt.assign (value := .int (Int.ofNat (tickSqrtInvert tick ratio).toNat)) ?_ ?_)
      ExecBlock.nil)
    · simpa only [hp, decide_true] using hgt
    · rw [tickSqrtInvert, if_pos hp]
      exact evalExpr_word_div (a := UInt256.lnot ⟨0⟩)
        (by simp only [evalExpr?, pure]; rfl) (evalExpr_var_get hr) (Nat.ne_of_gt hn)
    · exact assignLocalVarBase_frame hr
  · rw [tickSqrtInvertedFrame, if_neg hp]
    exact ExecStmt.iteFalse (by simpa only [hp, decide_false] using hgt) ExecBlock.nil

theorem tickSqrtInvertedFrame_values {frame : Frame} (tick : Int) (ratio : UInt256)
    (hr : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat)))
    (hs : frame.locals.get? "sqrtPriceX96" = some (.int 0)) :
    (tickSqrtInvertedFrame frame tick ratio).locals.get? "ratio" =
        some (.int (Int.ofNat (tickSqrtInvert tick ratio).toNat)) ∧
      (tickSqrtInvertedFrame frame tick ratio).locals.get? "sqrtPriceX96" = some (.int 0) := by
  change frame.locals["ratio"]? = _ at hr
  change frame.locals["sqrtPriceX96"]? = _ at hs
  by_cases hp : 0 < tick <;>
    simp [tickSqrtInvertedFrame, tickSqrtInvert, hp, hr, hs, Std.HashMap.getElem?_insert]

def tickSqrtRoundBitExpr : Expr :=
  .ite (.binary .eq (.binary .mod (.var "ratio") (.intLit 4294967296)) (.intLit 0))
    (.intLit 0) (.intLit 1)

def tickSqrtRoundExpr : Expr :=
  .cast
    (.cast
      (.binary .add (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "ratio") (.intLit 32))
        tickSqrtRoundBitExpr)
      (.elem (.int (.uint ⟨256, by decide⟩))))
    (.elem (.int (.uint ⟨160, by decide⟩)))

theorem evalTickSqrtRound {frame : Frame} {evm : EVM.State} (ratio : UInt256)
    (hr : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat))) :
    evalExpr? config frame evm tickSqrtRoundExpr =
      .ok (.int (Int.ofNat
        (UInt256.land (tickSqrtRound ratio) (UInt256.ofNat (2 ^ 160 - 1))).toNat)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hr
  have hm := evalExpr_word_mod he (b := UInt256.ofNat (2 ^ 32))
    (rhs := .intLit 4294967296) (by simp only [evalExpr?, pure]; rfl) (by decide)
  have hc := evalExpr_word_eq hm (b := ⟨0⟩) (rhs := .intLit 0)
    (by simp only [evalExpr?, pure]; rfl)
  have hb : evalExpr? config frame evm tickSqrtRoundBitExpr =
      .ok (.int (Int.ofNat
        (if UInt256.mod ratio (UInt256.ofNat (2 ^ 32)) = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat)) := by
    by_cases hz : UInt256.mod ratio (UInt256.ofNat (2 ^ 32)) = ⟨0⟩ <;>
      simp only [tickSqrtRoundBitExpr, evalExpr?, hc, hz, decide_true, decide_false,
        ↓reduceIte, pure, bind, EvalResult.bind] <;> rfl
  have hadd := evalExpr_word_add (evalExpr_word_shr 32 (by decide) he) hb
  change evalExpr? config frame evm
    (.cast (.binary .add
      (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "ratio") (.intLit 32))
      tickSqrtRoundBitExpr) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (Int.ofNat (tickSqrtRound ratio).toNat)) at hadd
  simp only [tickSqrtRoundExpr, evalExpr?, hadd, bind, EvalResult.bind, castValue?, EvalResult.ofOption]
  rw [normalizeUIntWord_mask ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide)]

theorem tickSqrtRoundSource {frame : Frame} {evm : EVM.State} (ratio : UInt256)
    (hr : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat)))
    (hs : frame.locals.get? "sqrtPriceX96" = some (.int 0)) :
    ∃ out, ExecBlock config frame evm (tickSqrtFunction.body.drop 24)
      (.returned out evm (some [.int (Int.ofNat
        (UInt256.land (tickSqrtRound ratio) (UInt256.ofNat (2 ^ 160 - 1))).toNat)])) := by
  let value := Value.int (Int.ofNat
    (UInt256.land (tickSqrtRound ratio) (UInt256.ofNat (2 ^ 160 - 1))).toNat)
  refine ⟨{frame with locals := frame.locals.insert "sqrtPriceX96" value}, ?_⟩
  refine ExecBlock.consNormal (ExecStmt.assign (evalTickSqrtRound ratio hr)
    (assignLocalVarBase_frame hs)) ?_
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp [evalExprs?, evalExpr?, value, EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem tickSqrtTailSource {frame : Frame} {evm : EVM.State} (tick : Int) (ratio : UInt256)
    (ht : frame.locals.get? "tick" = some (.int tick))
    (hr : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat)))
    (hs : frame.locals.get? "sqrtPriceX96" = some (.int 0)) (hn : 0 < ratio.toNat) :
    ∃ out, ExecBlock config frame evm (tickSqrtFunction.body.drop 23)
      (.returned out evm (some [.int (Int.ofNat
        (UInt256.land (tickSqrtRound (tickSqrtInvert tick ratio))
          (UInt256.ofNat (2 ^ 160 - 1))).toNat)])) := by
  obtain ⟨hr', hs'⟩ := tickSqrtInvertedFrame_values tick ratio hr hs
  obtain ⟨out, ho⟩ := tickSqrtRoundSource (evm := evm) (tickSqrtInvert tick ratio) hr' hs'
  exact ⟨out, ExecBlock.consNormal (tickSqrtInvertSource tick ratio ht hr hn) ho⟩

end Benchmarks.UniswapV3.Pool
