import Benchmarks.UniswapV4PoolManager.PoolSwapScanSyntax
import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.TickScanSource
import Benchmarks.UniswapV4PoolManager.TickClampPriceSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def poolSwapScanStep (s : PoolSwapStepWords) (evm : State) (id : UInt256)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) : PoolSwapStepWords :=
  let c := tickScanCompressed r.tick p.tickSpacing p.zeroForOne
  let masked := tickScanMasked evm id c p.zeroForOne
  {s with
    priceStart := r.price
    tickNext := tickScanResultWord c p.tickSpacing masked p.zeroForOne
    initialized := decide (masked ≠ ⟨0⟩)}

def poolSwapScanCallFrame (f : Frame) (s : PoolSwapStepWords) (evm : State) (id : UInt256)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) : Frame :=
  valueLocal (valueLocal (valueLocal f "step" (poolSwapStepValue {s with priceStart := r.price}))
    poolSwapBitmapAlias (tickBitmapRefValue id)) "__c12" (.tuple (tickScanValues evm id r.tick p.tickSpacing p.zeroForOne))

def poolSwapScanFrame (f : Frame) (s : PoolSwapStepWords) (evm : State) (id : UInt256)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) : Frame :=
  let after := poolSwapScanStep s evm id r p
  valueLocal (valueLocal (poolSwapScanCallFrame f s evm id r p) "step"
    (poolSwapStepValue {s with priceStart := r.price, tickNext := after.tickNext}))
    "step" (poolSwapStepValue after)

theorem poolSwapScanSource {f : Frame} {evm : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (htick : (EVM.signed r.tick).natAbs < 2^255)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hself : f.locals.get? "self" = some (poolRefValue id))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne)) :
    ExecBlock config f evm (poolSwapLoopBody.take 5) (.ok (poolSwapScanFrame f s evm id r p) evm) := by
  let f0 := valueLocal f "step" (poolSwapStepValue {s with priceStart := r.price})
  let f1 := valueLocal f0 poolSwapBitmapAlias (tickBitmapRefValue id)
  let f2 := poolSwapScanCallFrame f s evm id r p
  let after := poolSwapScanStep s evm id r p
  let f3 := valueLocal f2 "step" (poolSwapStepValue {s with priceStart := r.price, tickNext := after.tickNext})
  have hstart : ExecStmt config f evm poolSwapLoopBody[0]! (.ok f0 evm) :=
    ExecStmt.assign (evalStructField (evalLocalValue hr) rfl) (assignLocalField hs rfl rfl)
  have hself0 : f0.locals.get? "self" = some (poolRefValue id) :=
    (store_get_ne _ _ (by decide : ("step" == "self") = false)).trans hself
  have href : ExecStmt config f0 evm poolSwapLoopBody[1]! (.ok f1 evm) :=
    ExecStmt.letStorage (resolveStorageAliasField hself0 rfl)
  have hr1 : f1.locals.get? "result" = some (poolSwapResultValue r) :=
    (store_get_ne2 _ _ _ (by decide : ("step" == "result") = false)
      (by decide : (poolSwapBitmapAlias == "result") = false)).trans hr
  have hp1 : f1.locals.get? "params" = some (poolSwapParamsValue p) :=
    (store_get_ne2 _ _ _ (by decide : ("step" == "params") = false)
      (by decide : (poolSwapBitmapAlias == "params") = false)).trans hp
  have hz1 : f1.locals.get? "zeroForOne" = some (.bool p.zeroForOne) :=
    (store_get_ne2 _ _ _ (by decide : ("step" == "zeroForOne") = false)
      (by decide : (poolSwapBitmapAlias == "zeroForOne") = false)).trans hz
  have hcall : ExecStmt config f1 evm poolSwapLoopBody[2]! (.ok f2 evm) :=
    tickScanCall p.zeroForOne (show f1.contract = contract from hf) htick
      (evalLocalValue (store_get_self _ _ _)) (evalStructField (evalLocalValue hr1) rfl)
      (evalStructField (evalLocalValue hp1) rfl) (evalLocalValue hz1) "__c12"
  have hs2 : f2.locals.get? "step" = some (poolSwapStepValue {s with priceStart := r.price}) :=
    (store_get_ne2 _ _ _ (by decide : (poolSwapBitmapAlias == "step") = false)
      (by decide : ("__c12" == "step") = false)).trans (store_get_self _ _ _)
  have hv2 : f2.locals.get? "__c12" = some (.tuple (tickScanValues evm id r.tick p.tickSpacing p.zeroForOne)) :=
    store_get_self _ _ _
  have hnext : ExecStmt config f2 evm poolSwapLoopBody[3]! (.ok f3 evm) :=
    ExecStmt.assign (evalTupleProjection (evalLocalValue hv2) (i := 0) rfl)
      (poolSwapStep_tick_assign hs2 after.tickNext)
  have hv3 : f3.locals.get? "__c12" = some (.tuple (tickScanValues evm id r.tick p.tickSpacing p.zeroForOne)) :=
    (store_get_ne _ _ (by decide : ("step" == "__c12") = false)).trans hv2
  have hinit : ExecStmt config f3 evm poolSwapLoopBody[4]! (.ok (poolSwapScanFrame f s evm id r p) evm) :=
    ExecStmt.assign (evalTupleProjection (evalLocalValue hv3) (i := 1) rfl)
      (assignLocalField (store_get_self _ _ _) rfl rfl)
  exact ExecBlock.consNormal hstart (ExecBlock.consNormal href (ExecBlock.consNormal hcall
    (ExecBlock.consNormal hnext (execBlock_singleton hinit))))

theorem poolSwapScanFrame_step (f : Frame) (s : PoolSwapStepWords) (evm : State) (id : UInt256)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) :
    (poolSwapScanFrame f s evm id r p).locals.get? "step" = some (poolSwapStepValue (poolSwapScanStep s evm id r p)) :=
  store_get_self _ _ _

theorem poolSwapScanFrame_contract (f : Frame) (s : PoolSwapStepWords) (evm : State) (id : UInt256)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) : (poolSwapScanFrame f s evm id r p).contract = f.contract := by
  simp only [poolSwapScanFrame, poolSwapScanCallFrame, valueLocal_contract]

theorem poolSwapScanStep_tick_canonical (s : PoolSwapStepWords) (evm : State) (id : UInt256)
    (r : PoolSwapResultWords) (p : PoolSwapParamsWords) : int24Canonical (poolSwapScanStep s evm id r p).tickNext :=
  tickScanResultWord_canonical ..

theorem poolSwapScanPriceSource {f : Frame} {evm : State} {id : UInt256}
    {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}
    (hf : f.contract = contract) (htick : (EVM.signed r.tick).natAbs < 2^255)
    (hs : f.locals.get? "step" = some (poolSwapStepValue s))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hp : f.locals.get? "params" = some (poolSwapParamsValue p))
    (hself : f.locals.get? "self" = some (poolRefValue id))
    (hz : f.locals.get? "zeroForOne" = some (.bool p.zeroForOne)) :
    ExecBlock config f evm (poolSwapLoopBody.take 8)
      (.ok (tickClampPriceFrame (poolSwapScanFrame f s evm id r p) (poolSwapScanStep s evm id r p)) evm) :=
  execBlock_append (poolSwapScanSource hf htick hs hr hp hself hz)
    (tickClampPriceSource ((poolSwapScanFrame_contract ..).trans hf) (poolSwapScanFrame_step ..) (poolSwapScanStep_tick_canonical ..))

end Benchmarks.UniswapV4PoolManager
