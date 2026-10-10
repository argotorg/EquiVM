import Benchmarks.UniswapV4PoolManager.PoolSwapCrossSource
import Benchmarks.UniswapV4PoolManager.PoolSwapBoundaryTickSource
import Benchmarks.UniswapV4PoolManager.PoolSwapRepriceSource
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapCrossFrame_get (f : Frame) (evm : State) (id : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (zeroForOne : Bool) (key : Ident)
    (h0 : ("feeGrowthGlobal0X128" == key) = false) (h1 : ("feeGrowthGlobal1X128" == key) = false)
    (ha : (poolSwapCrossAlias == key) = false) (hn : ("liquidityNet" == key) = false)
    (hc : ("__c22" == key) = false) (hr : ("result" == key) = false) :
    (poolSwapCrossFrame f evm id s r zeroForOne).locals.get? key = f.locals.get? key := by
  unfold poolSwapCrossFrame
  simp only [valueLocal_get, hr, Bool.false_eq_true, if_false, wordLocal_get, hc]
  unfold poolSwapCrossNetFrame
  split <;> simp only [valueLocal_get, hn, Bool.false_eq_true, if_false,
    poolSwapCrossCallFrame, ha, wordLocal_get, h0, h1]

theorem poolSwapCrossFrame_result (f : Frame) (evm : State) (id : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (zeroForOne : Bool) :
    (poolSwapCrossFrame f evm id s r zeroForOne).locals.get? "result" =
      some (poolSwapResultValue {r with liquidity := poolSwapCrossLiquidity evm id s zeroForOne r.liquidity}) :=
  store_get_self _ _ _

def poolSwapTickResult (f : Frame) (evm : State) (id : UInt256) (s : PoolSwapStepWords)
    (r : PoolSwapResultWords) (zeroForOne : Bool) : ExecResult :=
  if r.price = s.priceNext then
    if s.initialized then
      if evm.executionEnv.perm = false then .staticViolation
      else if liquidityAddFits r.liquidity (EVM.signed (poolSwapCrossDelta zeroForOne (poolSwapCrossNet evm id s zeroForOne))) then
        .ok (valueLocal (poolSwapCrossFrame f evm id s r zeroForOne) "result"
          (poolSwapResultValue {r with
            tick := poolSwapBoundaryTick zeroForOne s.tickNext
            liquidity := poolSwapCrossLiquidity evm id s zeroForOne r.liquidity})) (poolSwapCrossPost evm id s zeroForOne)
      else .reverted
    else .ok (valueLocal f "result" (poolSwapResultValue {r with tick := poolSwapBoundaryTick zeroForOne s.tickNext})) evm
  else poolSwapRepriceResult f evm s r

theorem poolSwapTickSource {f : Frame} {evm : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {zeroForOne : Bool}
    (hf : f.contract = contract)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hself : f.locals.get? "self" = some (poolRefValue id))
    (hz : f.locals.get? "zeroForOne" = some (.bool zeroForOne)) :
    ExecStmt config f evm poolSwapLoopBody[18]! (poolSwapTickResult f evm id s r zeroForOne) := by
  have he := evalEqWords (evalStructField (cfg := config) (evm := evm) (field := "sqrtPriceX96") (evalLocalValue hr) rfl)
    (evalStructField (field := "sqrtPriceNextX96") (evalLocalValue hs) rfl)
  rw [poolSwapLoop_tick]
  unfold poolSwapTickResult
  by_cases heq : r.price = s.priceNext
  · rw [if_pos heq]
    apply ExecStmt.iteTrue (by simpa only [decide_eq_true heq] using he)
    have hi : evalExpr? config f evm (.field (.var "step") "initialized") = .ok (.bool s.initialized) :=
      evalStructField (evalLocalValue hs) rfl
    by_cases hinit : s.initialized = true
    · rw [if_pos hinit]
      have hcross := poolSwapCrossSource (evm := evm) hf hs hr hself hz
      unfold poolSwapCrossResult at hcross
      by_cases hp : evm.executionEnv.perm = false
      · rw [if_pos hp] at hcross ⊢
        exact ExecBlock.consStatic (ExecStmt.iteTrue (by rwa [hinit] at hi) hcross)
      · rw [if_neg hp] at hcross ⊢
        by_cases hfit : liquidityAddFits r.liquidity (EVM.signed (poolSwapCrossDelta zeroForOne (poolSwapCrossNet evm id s zeroForOne)))
        · rw [if_pos hfit] at hcross ⊢
          have hs' := (poolSwapCrossFrame_get f evm id s r zeroForOne "step"
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hs
          have hz' := (poolSwapCrossFrame_get f evm id s r zeroForOne "zeroForOne"
            (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)).trans hz
          have htail := poolSwapBoundaryTickSource
            (evm := poolSwapCrossPost evm id s zeroForOne)
            (r := {r with liquidity := poolSwapCrossLiquidity evm id s zeroForOne r.liquidity})
            hs' (poolSwapCrossFrame_result f evm id s r zeroForOne) hz'
          exact ExecBlock.consNormal (ExecStmt.iteTrue (by rwa [hinit] at hi) hcross)
            (execBlock_singleton htail)
        · rw [if_neg hfit] at hcross ⊢
          exact ExecBlock.consRevert (ExecStmt.iteTrue (by rwa [hinit] at hi) hcross)
    · rw [if_neg hinit]
      have hfalse : s.initialized = false := Bool.eq_false_of_not_eq_true hinit
      exact ExecBlock.consNormal (ExecStmt.iteFalse (by rwa [hfalse] at hi) ExecBlock.nil)
        (execBlock_singleton (poolSwapBoundaryTickSource hs hr hz))
  · rw [if_neg heq]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false heq] using he)
      (execBlock_singleton (poolSwapRepriceSource hf hs hr))

end Benchmarks.UniswapV4PoolManager
