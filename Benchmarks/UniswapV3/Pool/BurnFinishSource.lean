import Benchmarks.UniswapV3.Pool.BurnOwedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def burnFinalFrame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) : Frame :=
  if burnHasAmounts a0 a1 then burnOwedFrame v a key a0 a1 evm
  else burnAmountsFrame v a key a0 a1

def burnFinalState (key : UInt256) (a0 a1 : Int) (evm : EVM.State) : EVM.State :=
  if burnHasAmounts a0 a1 then burnOwedState key a0 a1 evm else evm

theorem burnOwedChoiceSource (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) :
    ExecStmt config (burnAmountsFrame v a key a0 a1) evm burnTransition.body[12]!
      (.ok (burnFinalFrame v a key a0 a1 evm) (burnFinalState key a0 a1 evm)) := by
  cases hh : burnHasAmounts a0 a1
  · simp only [burnFinalFrame, burnFinalState, hh, Bool.false_eq_true, if_false]
    exact ExecStmt.iteFalse (by simpa only [hh] using evalBurnHasAmounts v a key a0 a1 evm)
      ExecBlock.nil
  · simp only [burnFinalFrame, burnFinalState, hh, if_true]
    exact ExecStmt.iteTrue (by simpa only [hh] using evalBurnHasAmounts v a key a0 a1 evm)
      (burnOwedSource v a key a0 a1 evm)

theorem burnFinalFrame_eq (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) :
    burnFinalFrame v a key a0 a1 evm =
      {contract := contract, locals := (burnFinalFrame v a key a0 a1 evm).locals,
        immutables := immStore v} := by
  cases hh : burnHasAmounts a0 a1 <;> simp only [burnFinalFrame, hh, Bool.false_eq_true, if_false, if_true]
  all_goals rfl

theorem burnFinishSource (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) :
    ExecBlock config (burnFinalFrame v a key a0 a1 evm) (burnFinalState key a0 a1 evm)
      (burnTransition.body.drop 13)
      (.returned (burnFinalFrame v a key a0 a1 evm)
        (storeSlot0Unlocked (burnFinalState key a0 a1 evm) true)
        (some [.int (Int.ofNat (burnAmount a0).toNat), .int (Int.ofNat (burnAmount a1).toNat)])) := by
  have hget (name : Ident) : (burnFinalFrame v a key a0 a1 evm).locals.get? name =
      (if burnHasAmounts a0 a1 then (burnOwedFrame v a key a0 a1 evm).locals
        else (burnAmountsFrame v a key a0 a1).locals).get? name := by
    cases hh : burnHasAmounts a0 a1 <;> simp only [burnFinalFrame, hh, Bool.false_eq_true, if_false, if_true]
  have hl : (burnFinalFrame v a key a0 a1 evm).locals.get? "tickLower" = some (.int a.lower) := by
    rw [hget]; split <;> burn_owed_get
  have hu : (burnFinalFrame v a key a0 a1 evm).locals.get? "tickUpper" = some (.int a.upper) := by
    rw [hget]; split <;> burn_owed_get
  have ha : (burnFinalFrame v a key a0 a1 evm).locals.get? "amount" =
      some (.int (Int.ofNat a.amount.toNat)) := by rw [hget]; split <;> burn_owed_get
  have h0 : (burnFinalFrame v a key a0 a1 evm).locals.get? "amount0" =
      some (.int (Int.ofNat (burnAmount a0).toNat)) := by rw [hget]; split <;> burn_owed_get
  have h1 : (burnFinalFrame v a key a0 a1 evm).locals.get? "amount1" =
      some (.int (Int.ofNat (burnAmount a1).toNat)) := by rw [hget]; split <;> burn_owed_get
  have hs : (burnFinalFrame v a key a0 a1 evm).locals.get? "slot0" = none := by
    rw [hget]; split <;> burn_owed_get
  rw [burnFinalFrame_eq]
  refine ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.address (burnFinalState key a0 a1 evm).executionEnv.source, .int a.lower, .int a.upper,
      .int (Int.ofNat a.amount.toNat), .int (Int.ofNat (burnAmount a0).toNat),
      .int (Int.ofNat (burnAmount a1).toNat)]) ?_) ?_
  · simp only [evalExprs?, evalExpr?, hl, hu, ha, h0, h1, EvalResult.ofOption,
      envValue, bind, EvalResult.bind, pure]
  refine ExecBlock.consNormal (ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked _ _ _ true hs)) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  simp only [evalExprs?, evalExpr?, h0, h1, EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
