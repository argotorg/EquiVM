import Benchmarks.UniswapV3.Pool.ModifyPositionOutsideModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionOutsideChoiceSource (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (second : Bool) (result : ExecResult)
    (hz : a.delta ≠ 0)
    (hrange : if second then a.upper ≤ slot0TickValue evm.accountMap evm.executionEnv
      else slot0TickValue evm.accountMap evm.executionEnv < a.lower)
    (ht : validTicks a.lower a.upper)
    (hout : ExecBlock config (modifyPositionUpdatedFrame imms a evm) evm'
      (modifyPositionOutsideBody second) result) :
    ExecStmt config (modifyPositionUpdatedFrame imms a evm) evm'
      modifyPositionFunction.body[8]! result := by
  apply ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using
    evalModifyPositionNonzero imms a evm evm')
  apply execBlock_singleton
  have hl := evalModifyPositionRangeGuard imms a evm evm' false
  have hu := evalModifyPositionRangeGuard imms a evm evm' true
  cases second
  · change slot0TickValue evm.accountMap evm.executionEnv < a.lower at hrange
    apply ExecStmt.iteTrue
      (by simpa only [Bool.false_eq_true, if_false, decide_eq_true hrange] using hl)
    exact hout
  · have hnlo : ¬slot0TickValue evm.accountMap evm.executionEnv < a.lower := by
      have ho := ht.1
      change a.upper ≤ slot0TickValue evm.accountMap evm.executionEnv at hrange
      omega
    have hnup : ¬slot0TickValue evm.accountMap evm.executionEnv < a.upper := by
      change a.upper ≤ slot0TickValue evm.accountMap evm.executionEnv at hrange
      omega
    apply ExecStmt.iteFalse
      (by simpa only [Bool.false_eq_true, if_false, decide_eq_false hnlo] using hl)
    apply execBlock_singleton
    exact ExecStmt.iteFalse
      (by simpa only [if_true, decide_eq_false hnup] using hu) hout

theorem modifyPositionOutsideReturnSource (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (second : Bool) :
    ExecStmt config (modifyPositionOutsideFinalFrame imms a evm second) evm'
      (.return [.var "position", .var "amount0", .var "amount1"])
      (.returned (modifyPositionOutsideFinalFrame imms a evm second) evm'
        (some [modifyPositionKeyValue a,
          .int (if second then 0 else signedAmountDeltaResult second (modifyPositionOutsideArgs a)),
          .int (if second then signedAmountDeltaResult second (modifyPositionOutsideArgs a) else 0)])) := by
  have hk : evalExpr? config (modifyPositionOutsideFinalFrame imms a evm second) evm'
      (.var "position") = .ok (modifyPositionKeyValue a) :=
    evalExpr_var_get (by cases second <;> modify_position_outside_get)
  have h0 : evalExpr? config (modifyPositionOutsideFinalFrame imms a evm second) evm'
      (.var "amount0") = .ok (.int
        (if second then 0 else signedAmountDeltaResult second (modifyPositionOutsideArgs a))) :=
    evalExpr_var_get (by cases second <;> modify_position_outside_get)
  have h1 : evalExpr? config (modifyPositionOutsideFinalFrame imms a evm second) evm'
      (.var "amount1") = .ok (.int
        (if second then signedAmountDeltaResult second (modifyPositionOutsideArgs a) else 0)) :=
    evalExpr_var_get (by cases second <;> modify_position_outside_get)
  exact ExecStmt.return (by simp only [evalExprs?, hk, h0, h1, bind, EvalResult.bind, pure])

end Benchmarks.UniswapV3.Pool
