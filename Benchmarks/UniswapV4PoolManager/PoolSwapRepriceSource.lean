import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapTickSyntax
import Benchmarks.UniswapV4PoolManager.TickPriceSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapRepriceFrame (f : Frame) (r : PoolSwapResultWords) (tick : UInt256) : Frame :=
  valueLocal (valueLocal f "__c23" (.int (EVM.signed tick))) "result" (poolSwapResultValue {r with tick := tick})

def poolSwapRepriceResult (f : Frame) (evm : State) (s : PoolSwapStepWords) (r : PoolSwapResultWords) : ExecResult :=
  if r.price = s.priceStart then .ok f evm else
    match tickPriceResult r.price with
    | none => .reverted
    | some tick => .ok (poolSwapRepriceFrame f r tick) evm

theorem poolSwapRepriceSource {f : Frame} {evm : State} {s : PoolSwapStepWords} {r : PoolSwapResultWords}
    (hf : f.contract = contract)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r)) :
    ExecStmt config f evm poolSwapRepriceStmt (poolSwapRepriceResult f evm s r) := by
  have hne := evalNeWords (evalStructField (cfg := config) (evm := evm) (field := "sqrtPriceX96") (evalLocalValue hr) rfl)
    (evalStructField (field := "sqrtPriceStartX96") (evalLocalValue hs) rfl)
  unfold poolSwapRepriceResult
  by_cases he : r.price = s.priceStart
  · rw [if_pos he]
    exact ExecStmt.iteFalse (by simpa only [he, ne_eq, not_true_eq_false, decide_false] using hne) ExecBlock.nil
  · rw [if_neg he]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true he] using hne)
    have hcall := tickPriceCall (evm := evm) hf (evalStructField (field := "sqrtPriceX96") (evalLocalValue hr) rfl) "__c23"
    cases ht : tickPriceResult r.price with
    | none =>
      rw [ht] at hcall
      exact ExecBlock.consRevert hcall
    | some tick =>
      rw [ht] at hcall
      exact ExecBlock.consNormal hcall (execBlock_singleton (ExecStmt.assign
        (evalLocalValue (store_get_self _ _ _)) (assignLocalField
          ((store_get_ne _ _ (by decide : ("__c23" == "result") = false)).trans hr) rfl rfl)))

end Benchmarks.UniswapV4PoolManager
