import Benchmarks.UniswapV4PoolManager.PoolSwapFinishStorage
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapSlot0Frame (f : Frame) (packed : UInt256) (r : PoolSwapResultWords) : Frame :=
  valueLocal (valueLocal f "__c24" (wordBytes32Value (slot0SetTickWord packed r.tick)))
    "__c25" (wordBytes32Value (poolSwapSlot0Word packed r))

theorem poolSwapSlot0Frame_get (f : Frame) (packed : UInt256) (r : PoolSwapResultWords) (key : Ident)
    (h24 : ("__c24" == key) = false) (h25 : ("__c25" == key) = false) :
    (poolSwapSlot0Frame f packed r).locals.get? key = f.locals.get? key := by
  simp only [poolSwapSlot0Frame, valueLocal_get, h24, h25, Bool.false_eq_true, if_false]

theorem poolSwapLiquiditySource {f : Frame} {evm : State} {id : UInt256} {r : PoolSwapResultWords}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r)) (hl : r.liquidity.toNat < 2^128) :
    ExecStmt config f evm poolSwapFunction.body[32]! (.ok f (poolSwapLiquidityPost evm id r.liquidity)) := by
  have hg := evalNeWords (poolLiquidity_read (evm := evm) hs)
    (evalStructField (field := "liquidity") (evalLocalValue hr) rfl)
  by_cases he : poolLiquidityWord evm id = r.liquidity
  · rw [poolSwapLiquidityPost, if_pos he]
    exact ExecStmt.iteFalse (by simpa only [he, ne_eq, not_true_eq_false, decide_false] using hg) ExecBlock.nil
  · rw [poolSwapLiquidityPost, if_neg he]
    exact ExecStmt.iteTrue (by simpa only [decide_eq_true he] using hg)
      (execBlock_singleton (ExecStmt.assign
        (evalStructField (field := "liquidity") (evalLocalValue hr) rfl) (poolLiquidity_write hs hl)))

theorem poolSwapGrowthStoreSource {f : Frame} {evm : State} {id : UInt256} {s : PoolSwapStepWords}
    {zeroForOne : Bool}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (ht : f.locals.get? "step" = some (poolSwapStepValue s))
    (hz : f.locals.get? "zeroForOne" = some (.bool zeroForOne)) :
    ExecStmt config f evm poolSwapFunction.body[33]!
      (.ok f (poolSwapGrowthPost evm id s.feeGrowthGlobal zeroForOne)) := by
  have hg := evalNotBool (evalLocalValue (cfg := config) (evm := evm) hz)
  have hv := evalStructField (field := "feeGrowthGlobalX128") (evalLocalValue (cfg := config) (evm := evm) ht) rfl
  cases zeroForOne
  · exact ExecStmt.iteTrue hg (execBlock_singleton (ExecStmt.assign hv (poolFeeGrowth_write hs true)))
  · exact ExecStmt.iteFalse hg (execBlock_singleton (ExecStmt.assign hv (poolFeeGrowth_write hs false)))

theorem poolSwapStoreSource {f : Frame} {evm : State} {id packed : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {zeroForOne : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (ht : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hz : f.locals.get? "zeroForOne" = some (.bool zeroForOne))
    (hslot : f.locals.get? "slot0Start" = some (wordBytes32Value packed))
    (hp : r.price.toNat < 2^160) (hl : r.liquidity.toNat < 2^128) :
    ExecBlock config f evm ((poolSwapFunction.body.drop 29).take 5)
      (if evm.executionEnv.perm = false then .staticViolation else
        .ok (poolSwapSlot0Frame f packed r) (poolSwapFinishPost evm id packed s r zeroForOne)) := by
  let f1 := valueLocal f "__c24" (wordBytes32Value (slot0SetTickWord packed r.tick))
  let f2 := poolSwapSlot0Frame f packed r
  have htick : ExecStmt config f evm poolSwapFunction.body[29]! (.ok f1 evm) :=
    slot0SetTickCall hf (evalLocalValue hslot)
      (evalStructField (field := "tick") (evalLocalValue hr) rfl) "__c24"
  have hr1 : f1.locals.get? "result" = some (poolSwapResultValue r) :=
    (store_get_ne _ _ (by decide : ("__c24" == "result") = false)).trans hr
  have hprice : ExecStmt config f1 evm poolSwapFunction.body[30]! (.ok f2 evm) :=
    slot0SetSqrtCall (f := f1) hf hp (evalLocalValue (store_get_self _ _ _))
      (evalStructField (field := "sqrtPriceX96") (evalLocalValue hr1) rfl) "__c25"
  have hget := poolSwapSlot0Frame_get f packed r
  have hs2 := (hget "self" (by decide) (by decide)).trans hs
  have hr2 := (hget "result" (by decide) (by decide)).trans hr
  have ht2 := (hget "step" (by decide) (by decide)).trans ht
  have hz2 := (hget "zeroForOne" (by decide) (by decide)).trans hz
  have hv := evalLocalValue (cfg := config) (f := f2) (evm := evm) (store_get_self _ _ _)
  have hw := poolSlot0_write (f := f2) (evm := evm) hs2 (poolSwapSlot0Word packed r)
  by_cases hperm : evm.executionEnv.perm = false
  · rw [if_pos hperm]
    exact ExecBlock.consNormal htick (ExecBlock.consNormal hprice
      (ExecBlock.consStatic (ExecStmt.assignStatic hv hw hperm)))
  · rw [if_neg hperm]
    exact ExecBlock.consNormal htick (ExecBlock.consNormal hprice
      (ExecBlock.consNormal (ExecStmt.assign hv hw)
        (ExecBlock.consNormal (poolSwapLiquiditySource hs2 hr2 hl)
          (execBlock_singleton (poolSwapGrowthStoreSource hs2 ht2 hz2)))))

end Benchmarks.UniswapV4PoolManager
