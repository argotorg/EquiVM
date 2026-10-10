import Benchmarks.UniswapV3.Pool.TickSqrtModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickSqrtFunction : FunctionDecl := contract.functions[17]!

theorem tickSqrtLookup :
    lookupCallable? contract "TickMath_getSqrtRatioAtTick" = some tickSqrtFunction.toCallable := rfl

def tickSqrtLocals (tick : Int) : Store := (∅ : Store).insert "tick" (.int tick)

def tickSqrtFrame (imms : Store) (tick : Int) : Frame :=
  {contract := contract, locals := tickSqrtLocals tick, immutables := imms}

theorem tickSqrtBind (tick : Int) :
    bindParams? tickSqrtFunction.params [.int tick] = some (tickSqrtLocals tick) := rfl

def tickSqrtZeroFrame (imms : Store) (tick : Int) : Frame :=
  {tickSqrtFrame imms tick with locals := (tickSqrtLocals tick).insert "sqrtPriceX96" (.int 0)}

def tickSqrtAbsFrame (imms : Store) (tick : Int) : Frame :=
  {tickSqrtZeroFrame imms tick with
    locals := (tickSqrtZeroFrame imms tick).locals.insert
      "absTick" (.int (Int.ofNat (UInt256.ofNat tick.natAbs).toNat))}

def tickSqrtAbsExpr : Expr :=
  .ite (.binary .lt (.var "tick") (.intLit 0))
    (.cast
      (.cast
        (.binary .sub (.intLit 0) (.cast (.var "tick") (.elem (.int (.sint ⟨256, by decide⟩)))))
        (.elem (.int (.sint ⟨256, by decide⟩))))
      (.elem (.int (.uint ⟨256, by decide⟩))))
    (.cast (.cast (.var "tick") (.elem (.int (.sint ⟨256, by decide⟩))))
      (.elem (.int (.uint ⟨256, by decide⟩))))

theorem tickSqrtAbs_lt (tick : Int) (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) :
    tick.natAbs < 2 ^ 24 := by
  have h : (tick.natAbs : Int) < 2 ^ 24 := by
    rw [Int.natCast_natAbs, abs_lt]
    constructor <;> omega
  exact_mod_cast h

theorem evalTickSqrtAbs {frame : Frame} {evm : EVM.State} (tick : Int)
    (ht : frame.locals.get? "tick" = some (.int tick))
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) :
    evalExpr? config frame evm tickSqrtAbsExpr =
      .ok (.int (Int.ofNat (UInt256.ofNat tick.natAbs).toNat)) := by
  have hc : normalizeInt (.sint ⟨256, by decide⟩) tick = tick := by
    norm_num only [normalizeInt, EVM.twoPow]
    split <;> omega
  have hn : normalizeInt (.sint ⟨256, by decide⟩) (0 - tick) = 0 - tick := by
    norm_num only [normalizeInt, EVM.twoPow]
    split <;> omega
  have ha := tickSqrtAbs_lt tick hlo hhi
  rw [UInt256.toNat_ofNat_of_lt (lt_trans ha (by decide))]
  have he := evalExpr_var_get (cfg := config) (evm := evm) ht
  by_cases htick : tick < 0
  · have habs : Int.ofNat tick.natAbs = -tick := by
      simpa only [Int.ofNat_eq_natCast, Int.natCast_natAbs, abs_of_neg htick]
    simp only [tickSqrtAbsExpr, evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind,
      castValue?, EvalResult.ofOption, pure, htick, decide_true, hc, hn]
    rw [normalizeInt_uint_eq_self _ _ (by omega) (by change 0 - tick < 2 ^ 256; omega)]
    simp only [habs, zero_sub]
  · have habs : Int.ofNat tick.natAbs = tick := Int.natAbs_of_nonneg (by omega)
    simp only [tickSqrtAbsExpr, evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind,
      castValue?, EvalResult.ofOption, pure, htick, decide_false, hc]
    rw [normalizeInt_uint_eq_self _ _ (by omega) (by change tick < 2 ^ 256; omega), habs]

theorem tickSqrtPrefixSource (imms : Store) (evm : EVM.State) (tick : Int)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) :
    ExecBlock config (tickSqrtFrame imms tick) evm (tickSqrtFunction.body.take 2)
      (.ok (tickSqrtAbsFrame imms tick) evm) := by
  refine ExecBlock.consNormal (solm' := tickSqrtZeroFrame imms tick)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl ?_) ExecBlock.nil
  exact evalTickSqrtAbs tick
    (by simp [tickSqrtZeroFrame, tickSqrtFrame, tickSqrtLocals, Std.HashMap.getElem_insert]) hlo hhi

theorem evalTickSqrtGuard (imms : Store) (evm : EVM.State) (tick : Int)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23) :
    evalExpr? config (tickSqrtAbsFrame imms tick) evm
      (.binary .le (.var "absTick")
        (.cast (.cast (.binary .sub (.intLit 0) (.unary .neg (.intLit 887272)))
          (.elem (.int (.sint ⟨24, by decide⟩)))) (.elem (.int (.uint ⟨256, by decide⟩))))) =
      .ok (.bool (decide (tick.natAbs ≤ 887272))) := by
  have ha := tickSqrtAbs_lt tick hlo hhi
  simp [evalExpr?, tickSqrtAbsFrame, Std.HashMap.getElem_insert, EvalResult.ofOption,
    evalBinaryOp?, evalUnaryOp?, castValue?, normalizeInt, EVM.twoPow,
    bind, EvalResult.bind, pure,
    UInt256.toNat_ofNat_of_lt (lt_trans ha (by decide : 2 ^ 24 < UInt256.size))]
  rw [← Int.natCast_natAbs]
  exact Int.ofNat_le

theorem tickSqrtReverts (imms : Store) (evm : EVM.State) (tick : Int)
    (hlo : -(2 ^ 23 : Int) ≤ tick) (hhi : tick < 2 ^ 23)
    (h : ¬ tick.natAbs ≤ 887272) :
    ExecFuncBody config (tickSqrtFrame imms tick) evm tickSqrtFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 tickSqrtFunction.body]
  apply execBlock_append_ok (tickSqrtPrefixSource imms evm tick hlo hhi)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [h, decide_false] using evalTickSqrtGuard imms evm tick hlo hhi

end Benchmarks.UniswapV3.Pool
