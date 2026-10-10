import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolSwapSyntax
import Benchmarks.UniswapV4PoolManager.SwapTargetSource
import Benchmarks.UniswapV4PoolManager.SwapStepSource
import Benchmarks.UniswapV4PoolManager.ValueLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapComputeStep (s : PoolSwapStepWords) (next : UInt256) (w : SwapStepWords) : PoolSwapStepWords :=
  {s with priceNext := next, amountIn := w.amountIn, amountOut := w.amountOut, feeAmount := w.fee}

def poolSwapComputeCallFrame (f : Frame) (s : PoolSwapStepWords) (p : PoolSwapParamsWords) (next : UInt256) : Frame :=
  wordLocal (valueLocal f "step" (poolSwapStepValue {s with priceNext := next})) "__c14"
    (swapTargetWord p.zeroForOne next p.priceLimit)

def poolSwapComputeFrame (f : Frame) (s : PoolSwapStepWords) (r : PoolSwapResultWords) (p : PoolSwapParamsWords)
    (next remaining fee : UInt256) : Frame :=
  let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  let f3 := swapStepCallFrame (poolSwapComputeCallFrame f s p next) "__c15" w
  let f4 := valueLocal f3 "result" (poolSwapResultValue {r with price := w.next})
  let f5 := valueLocal f4 "step" (poolSwapStepValue {s with priceNext := next, amountIn := w.amountIn})
  let f6 := valueLocal f5 "step" (poolSwapStepValue {s with priceNext := next, amountIn := w.amountIn, amountOut := w.amountOut})
  valueLocal f6 "step" (poolSwapStepValue (poolSwapComputeStep s next w))

theorem poolSwapComputeSource {f : Frame} {evm : State}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords} {next remaining fee : UInt256}
    (hf : f.contract = contract) (hrc : r.price.toNat < 2^160)
    (hnc : next.toNat < 2^160) (hlc : p.priceLimit.toNat < 2^160)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne))
    (hn : f.locals.get? "__c13" = some (.int (Int.ofNat next.toNat)))
    (hrem : f.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)))
    (hfee : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat))) :
    ExecBlock config f evm ((poolSwapLoopBody.drop 8).take 7)
      (if swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee then
        .ok (poolSwapComputeFrame f s r p next remaining fee) evm else .reverted) := by
  let f1 := valueLocal f "step" (poolSwapStepValue {s with priceNext := next})
  let f2 := poolSwapComputeCallFrame f s p next
  let w := swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  let f3 := swapStepCallFrame f2 "__c15" w
  let f4 := valueLocal f3 "result" (poolSwapResultValue {r with price := w.next})
  let f5 := valueLocal f4 "step" (poolSwapStepValue {s with priceNext := next, amountIn := w.amountIn})
  let f6 := valueLocal f5 "step" (poolSwapStepValue {s with priceNext := next, amountIn := w.amountIn, amountOut := w.amountOut})
  have hnext : ExecStmt config f evm poolSwapLoopBody[8]! (.ok f1 evm) :=
    ExecStmt.assign (evalLocalValue hn) (assignLocalField hs rfl rfl)
  have hz1 : f1.locals.get? "zeroForOne" = some (.bool p.zeroForOne) :=
    (store_get_ne _ _ (by decide : ("step" == "zeroForOne") = false)).trans hz
  have hp1 : f1.locals.get? "params" = some (poolSwapParamsValue p) :=
    (store_get_ne _ _ (by decide : ("step" == "params") = false)).trans hp
  have htarget : ExecStmt config f1 evm poolSwapLoopBody[9]! (.ok f2 evm) :=
    swapTargetCall (f := f1) p.zeroForOne hf (evalLocalValue hz1)
      (evalStructField (evalLocalValue (store_get_self _ _ _)) rfl)
      (evalStructField (evalLocalValue hp1) rfl) "__c14"
  have hr2 : f2.locals.get? "result" = some (poolSwapResultValue r) :=
    (store_get_ne2 _ _ _ (by decide : ("step" == "result") = false)
      (by decide : ("__c14" == "result") = false)).trans hr
  have hrem2 : f2.locals.get? "amountSpecifiedRemaining" = some (.int (EVM.signed remaining)) :=
    (store_get_ne2 _ _ _ (by decide : ("step" == "amountSpecifiedRemaining") = false)
      (by decide : ("__c14" == "amountSpecifiedRemaining") = false)).trans hrem
  have hfee2 : f2.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("step" == "swapFee") = false)
      (by decide : ("__c14" == "swapFee") = false)).trans hfee
  have hcompute := swapStepCall (f := f2) (evm := evm) hf hrc (swapTargetWord_canonical hnc hlc)
    (evalStructField (field := "sqrtPriceX96") (evalLocalValue hr2) rfl) (evalLocalValue (store_get_self _ _ _))
    (evalStructField (field := "liquidity") (evalLocalValue hr2) rfl)
    (evalLocalValue hrem2) (evalLocalValue hfee2) "__c15"
  by_cases hfit : swapStepFits r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee
  · rw [if_pos hfit] at hcompute ⊢
    have hv3 : f3.locals.get? "__c15" = some (.tuple (swapStepReturnValues w)) := store_get_self _ _ _
    have hr3 : f3.locals.get? "result" = some (poolSwapResultValue r) :=
      (store_get_ne _ _ (by decide : ("__c15" == "result") = false)).trans hr2
    have hs4 : f4.locals.get? "step" = some (poolSwapStepValue {s with priceNext := next}) :=
      (store_get_ne3 _ _ _ _ (by decide : ("__c14" == "step") = false)
        (by decide : ("__c15" == "step") = false) (by decide : ("result" == "step") = false)).trans
        (store_get_self _ _ _)
    have hprice : ExecStmt config f3 evm poolSwapLoopBody[11]! (.ok f4 evm) :=
      ExecStmt.assign (evalTupleProjection (evalLocalValue hv3) (i := 0) rfl) (assignLocalField hr3 rfl rfl)
    have hv4 : f4.locals.get? "__c15" = some (.tuple (swapStepReturnValues w)) :=
      (store_get_ne _ _ (by decide : ("result" == "__c15") = false)).trans hv3
    have hin : ExecStmt config f4 evm poolSwapLoopBody[12]! (.ok f5 evm) :=
      ExecStmt.assign (evalTupleProjection (evalLocalValue hv4) (i := 1) rfl) (assignLocalField hs4 rfl rfl)
    have hv5 : f5.locals.get? "__c15" = some (.tuple (swapStepReturnValues w)) :=
      (store_get_ne _ _ (by decide : ("step" == "__c15") = false)).trans hv4
    have hout : ExecStmt config f5 evm poolSwapLoopBody[13]! (.ok f6 evm) :=
      ExecStmt.assign (evalTupleProjection (evalLocalValue hv5) (i := 2) rfl)
        (assignLocalField (store_get_self _ _ _) rfl rfl)
    have hv6 : f6.locals.get? "__c15" = some (.tuple (swapStepReturnValues w)) :=
      (store_get_ne _ _ (by decide : ("step" == "__c15") = false)).trans hv5
    have hfee' : ExecStmt config f6 evm poolSwapLoopBody[14]! (.ok (poolSwapComputeFrame f s r p next remaining fee) evm) :=
      ExecStmt.assign (evalTupleProjection (evalLocalValue hv6) (i := 3) rfl)
        (assignLocalField (store_get_self _ _ _) rfl rfl)
    exact ExecBlock.consNormal hnext (ExecBlock.consNormal htarget (ExecBlock.consNormal hcompute
      (ExecBlock.consNormal hprice (ExecBlock.consNormal hin (ExecBlock.consNormal hout (execBlock_singleton hfee'))))))
  · rw [if_neg hfit] at hcompute ⊢
    exact ExecBlock.consNormal hnext (ExecBlock.consNormal htarget (ExecBlock.consRevert hcompute))

theorem poolSwapComputeFrame_contract (f : Frame) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (p : PoolSwapParamsWords) (next remaining fee : UInt256) :
    (poolSwapComputeFrame f s r p next remaining fee).contract = f.contract := by
  simp only [poolSwapComputeFrame, poolSwapComputeCallFrame, swapStepCallFrame,
    valueLocal_contract, wordLocal_contract]

theorem poolSwapComputeFrame_step (f : Frame) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (p : PoolSwapParamsWords) (next remaining fee : UInt256) :
    (poolSwapComputeFrame f s r p next remaining fee).locals.get? "step" =
      some (poolSwapStepValue (poolSwapComputeStep s next
        (swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee))) :=
  store_get_self _ _ _

theorem poolSwapComputeFrame_result (f : Frame) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (p : PoolSwapParamsWords) (next remaining fee : UInt256) :
    (poolSwapComputeFrame f s r p next remaining fee).locals.get? "result" =
      some (poolSwapResultValue {r with price :=
        (swapStepWord r.price (swapTargetWord p.zeroForOne next p.priceLimit) r.liquidity remaining fee).next}) :=
  (store_get_ne3 _ _ _ _ (by decide : ("step" == "result") = false)
    (by decide : ("step" == "result") = false) (by decide : ("step" == "result") = false)).trans (store_get_self _ _ _)

theorem poolSwapComputeFrame_get (f : Frame) (s : PoolSwapStepWords) (r : PoolSwapResultWords)
    (p : PoolSwapParamsWords) (next remaining fee : UInt256) (key : Ident)
    (hs : ("step" == key) = false) (hr : ("result" == key) = false)
    (h14 : ("__c14" == key) = false) (h15 : ("__c15" == key) = false) :
    (poolSwapComputeFrame f s r p next remaining fee).locals.get? key = f.locals.get? key := by
  have hcall (ff : Frame) (w : SwapStepWords) : swapStepCallFrame ff "__c15" w =
      valueLocal ff "__c15" (.tuple (swapStepReturnValues w)) := rfl
  simp only [poolSwapComputeFrame, poolSwapComputeCallFrame, hcall,
    valueLocal_get, wordLocal_get, hs, hr, h14, h15, Bool.false_eq_true, if_false]

end Benchmarks.UniswapV4PoolManager
