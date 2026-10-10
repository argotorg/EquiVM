import Benchmarks.UniswapV3.Pool.UpdatePositionFeeModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem evalUpdatePositionFeeExprs (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm evm' : EVM.State) :
    evalExprs? config (updatePositionChangedFrame v a evm) evm' updatePositionFeeExprs =
      .ok [.int a.lower, .int a.upper, .int a.current,
        .int (Int.ofNat (feeGrowthWord false evm.accountMap evm.executionEnv).toNat),
        .int (Int.ofNat (feeGrowthWord true evm.accountMap evm.executionEnv).toNat)] := by
  have hl : evalExpr? config (updatePositionChangedFrame v a evm) evm' (.var "tickLower") =
      .ok (.int a.lower) := evalExpr_var_get (by update_position_changed_get)
  have hu : evalExpr? config (updatePositionChangedFrame v a evm) evm' (.var "tickUpper") =
      .ok (.int a.upper) := evalExpr_var_get (by update_position_changed_get)
  have ht : evalExpr? config (updatePositionChangedFrame v a evm) evm' (.var "tick") =
      .ok (.int a.current) := evalExpr_var_get (by update_position_changed_get)
  have hg0 : evalExpr? config (updatePositionChangedFrame v a evm) evm'
      (.var "_feeGrowthGlobal0X128") =
      .ok (.int (Int.ofNat (feeGrowthWord false evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_var_get (by update_position_changed_get)
  have hg1 : evalExpr? config (updatePositionChangedFrame v a evm) evm'
      (.var "_feeGrowthGlobal1X128") =
      .ok (.int (Int.ofNat (feeGrowthWord true evm.accountMap evm.executionEnv).toNat)) :=
    evalExpr_var_get (by update_position_changed_get)
  simp only [updatePositionFeeExprs, evalExprs?, hl, hu, ht, hg0, hg1, bind, EvalResult.bind, pure]

theorem updatePositionFeeCallSource (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) :
    ExecStmt config (updatePositionChangedFrame v a evm) (updatePositionChangedState v a evm)
      (.internalCall "Tick_getFeeGrowthInside" updatePositionFeeExprs "__c7")
      (.ok (updatePositionFeeFrame v a evm) (updatePositionChangedState v a evm)) := by
  have hf : {updatePositionChangedFrame v a evm with
      locals := tickFeeLocals (updatePositionFeeArgs a evm)} =
      tickFeeFrame (immStore v) (updatePositionFeeArgs a evm) := by
    rw [updatePositionChangedFrame_eq]; rfl
  exact internalCallFunctionReturn (callee := tickFeeFunction)
    (argVals := [.int a.lower, .int a.upper, .int a.current,
      .int (Int.ofNat (feeGrowthWord false evm.accountMap evm.executionEnv).toNat),
      .int (Int.ofNat (feeGrowthWord true evm.accountMap evm.executionEnv).toNat)])
    (locals := tickFeeLocals (updatePositionFeeArgs a evm))
    (calleeSolm := tickFeeFinalFrame (immStore v) (updatePositionFeeArgs a evm)
      (updatePositionChangedState v a evm))
    (value := some [.int (Int.ofNat (updatePositionInside v a evm false).toNat),
      .int (Int.ofNat (updatePositionInside v a evm true).toNat)])
    (evalUpdatePositionFeeExprs v a evm _) (by rw [updatePositionChangedFrame_eq]; exact tickFeeLookup)
    (tickFeeBind (updatePositionFeeArgs a evm))
    (by
      rw [hf]
      exact tickFeeReturns (immStore v) (updatePositionChangedState v a evm)
        (updatePositionFeeArgs a evm))

theorem updatePositionFeeSource (v : UniswapV3PoolImmutables) (a : UpdatePositionArgs)
    (evm : EVM.State) :
    ExecBlock config (updatePositionChangedFrame v a evm) (updatePositionChangedState v a evm)
      updatePositionFeeBody (.ok (updatePositionFee1Frame v a evm) (updatePositionChangedState v a evm)) := by
  refine ExecBlock.consNormal (updatePositionFeeCallSource v a evm) ?_
  refine ExecBlock.consNormal (solm' := updatePositionFee0Frame v a evm)
    (evm' := updatePositionChangedState v a evm) (ExecStmt.letDecl ?_) ?_
  · simp only [evalExpr?, updatePositionFeeFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert_self, EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?]
    rfl
  exact ExecBlock.consNormal (ExecStmt.letDecl (by
    simp only [evalExpr?, updatePositionFee0Frame, updatePositionFeeFrame,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption,
      bind, EvalResult.bind, tupleGetValue?]; rfl)) ExecBlock.nil

end Benchmarks.UniswapV3.Pool
