import Benchmarks.UniswapV3.Pool.TickSqrtPrefix
import Benchmarks.UniswapV3.Pool.TickSqrtFactorsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickSqrtInitialExpr : Expr :=
  .ite (tickSqrtBitExpr 1) (.intLit 340265354078544963557816517032075149313)
    (.intLit 340282366920938463463374607431768211456)

def tickSqrtReadyFrame (imms : Store) (tick : Int) : Frame :=
  {tickSqrtAbsFrame imms tick with
    locals := (tickSqrtAbsFrame imms tick).locals.insert "ratio"
      (.int (Int.ofNat (tickSqrtInitial (UInt256.ofNat tick.natAbs)).toNat))}

theorem evalTickSqrtInitial {frame : Frame} {evm : EVM.State} (absTick : UInt256)
    (ha : frame.locals.get? "absTick" = some (.int (Int.ofNat absTick.toNat))) :
    evalExpr? config frame evm tickSqrtInitialExpr =
      .ok (.int (Int.ofNat (tickSqrtInitial absTick).toNat)) := by
  have he := evalTickSqrtBit (evm := evm) absTick 1 ha (by decide)
  change evalExpr? config frame evm (tickSqrtBitExpr 1) =
    .ok (.bool (decide (UInt256.land absTick ⟨1⟩ ≠ ⟨0⟩))) at he
  by_cases hz : UInt256.land absTick ⟨1⟩ = ⟨0⟩
  · simp only [tickSqrtInitialExpr, evalExpr?, he, tickSqrtInitial, hz, ne_eq,
      not_true_eq_false, decide_false, ↓reduceIte, pure, bind, EvalResult.bind]
    rfl
  · simp only [tickSqrtInitialExpr, evalExpr?, he, tickSqrtInitial, hz, ne_eq,
      not_false_eq_true, decide_true, ↓reduceIte, pure, bind, EvalResult.bind]
    rfl

theorem tickSqrtReadySource (imms : Store) (evm : EVM.State) (tick : Int)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) (h : tick.natAbs ≤ 887272) :
    ExecBlock config (tickSqrtFrame imms tick) evm (tickSqrtFunction.body.take 4)
      (.ok (tickSqrtReadyFrame imms tick) evm) := by
  change ExecBlock _ _ _
    (tickSqrtFunction.body.take 2 ++ (tickSqrtFunction.body.drop 2).take 2) _
  apply execBlock_append_ok (tickSqrtPrefixSource imms evm tick hlo hhi)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [h, decide_true] using evalTickSqrtGuard imms evm tick hlo hhi
  refine ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  exact evalTickSqrtInitial _ (by simp [tickSqrtAbsFrame])

theorem tickSqrtRatiosSource (imms : Store) (evm : EVM.State) (tick : Int)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) (h : tick.natAbs ≤ 887272) :
    ∃ frame, ExecBlock config (tickSqrtFrame imms tick) evm (tickSqrtFunction.body.take 23)
      (.ok frame evm) ∧
      frame.locals.get? "ratio" =
        some (.int (Int.ofNat (tickSqrtRatio (UInt256.ofNat tick.natAbs)).toNat)) ∧
      frame.locals.get? "tick" = some (.int tick) ∧
      frame.locals.get? "sqrtPriceX96" = some (.int 0) := by
  obtain ⟨frame, hb, hr, hp⟩ := tickSqrtFoldSource
    (frame := tickSqrtReadyFrame imms tick) (evm := evm)
    (UInt256.ofNat tick.natAbs) (tickSqrtInitial (UInt256.ofNat tick.natAbs)) tickSqrtFactors
    (by simp [tickSqrtReadyFrame, tickSqrtAbsFrame, Std.HashMap.getElem_insert])
    (by simp [tickSqrtReadyFrame]) (by decide +kernel)
  refine ⟨frame, ?_, hr, ?_, ?_⟩
  · change ExecBlock _ _ _ (tickSqrtFunction.body.take 4 ++
      tickSqrtFactors.map tickSqrtStepStmt) _
    exact execBlock_append_ok (tickSqrtReadySource imms evm tick hlo hhi h) hb
  · rw [hp "tick" (by decide)]
    simp [tickSqrtReadyFrame, tickSqrtAbsFrame, tickSqrtZeroFrame, tickSqrtFrame,
      tickSqrtLocals, Std.HashMap.getElem_insert]
  · rw [hp "sqrtPriceX96" (by decide)]
    simp [tickSqrtReadyFrame, tickSqrtAbsFrame, tickSqrtZeroFrame, Std.HashMap.getElem_insert]

end Benchmarks.UniswapV3.Pool
