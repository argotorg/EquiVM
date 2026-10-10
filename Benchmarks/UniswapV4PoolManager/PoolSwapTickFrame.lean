import Benchmarks.UniswapV4PoolManager.PoolSwapTickWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapCrossFrame_contract (f : Frame) (evm : State) (id : UInt256)
    (s : PoolSwapStepWords) (r : PoolSwapResultWords) (zeroForOne : Bool) :
    (poolSwapCrossFrame f evm id s r zeroForOne).contract = f.contract := by
  simp only [poolSwapCrossFrame, valueLocal_contract, wordLocal_contract]
  unfold poolSwapCrossNetFrame
  split <;> simp only [poolSwapCrossCallFrame, valueLocal_contract, wordLocal_contract]

def PoolSwapTickFramePost (f ff : Frame) (evm post : State) (r' : PoolSwapResultWords) : Prop :=
  ff.contract = f.contract ∧ post.executionEnv = evm.executionEnv ∧
  ff.locals.get? "result" = some (poolSwapResultValue r') ∧
  ∀ key : Ident, ("feeGrowthGlobal0X128" == key) = false → ("feeGrowthGlobal1X128" == key) = false →
    (poolSwapCrossAlias == key) = false → ("liquidityNet" == key) = false →
    ("__c22" == key) = false → ("__c23" == key) = false → ("result" == key) = false →
    ff.locals.get? key = f.locals.get? key

theorem poolSwapFramePost_store_result (f ff : Frame) (evm post : State) (r' : PoolSwapResultWords)
    (hc : ff.contract = f.contract) (he : post.executionEnv = evm.executionEnv)
    (hg : ∀ key : Ident, ("feeGrowthGlobal0X128" == key) = false → ("feeGrowthGlobal1X128" == key) = false →
      (poolSwapCrossAlias == key) = false → ("liquidityNet" == key) = false →
      ("__c22" == key) = false → ("__c23" == key) = false → ("result" == key) = false →
      ff.locals.get? key = f.locals.get? key) :
    PoolSwapTickFramePost f (valueLocal ff "result" (poolSwapResultValue r')) evm post r' := by
  refine ⟨hc, he, store_get_self _ _ _, ?_⟩
  intro key h0 h1 ha hn h22 h23 hk
  exact (store_get_ne _ _ hk).trans (hg key h0 h1 ha hn h22 h23 hk)

theorem poolSwapCrossFrame_post (f : Frame) (evm : State) (id : UInt256)
    (s : PoolSwapStepWords) (r : PoolSwapResultWords) (zeroForOne : Bool) :
    let r' := {r with
      tick := poolSwapBoundaryTick zeroForOne s.tickNext
      liquidity := poolSwapCrossLiquidity evm id s zeroForOne r.liquidity}
    PoolSwapTickFramePost f (valueLocal (poolSwapCrossFrame f evm id s r zeroForOne) "result" (poolSwapResultValue r'))
      evm (poolSwapCrossPost evm id s zeroForOne) r' := by
  dsimp only
  apply poolSwapFramePost_store_result
  · exact poolSwapCrossFrame_contract f evm id s r zeroForOne
  · exact tickCrossPost_executionEnv evm id (EVM.signed s.tickNext)
      (poolSwapCrossGrowth0 evm id s zeroForOne) (poolSwapCrossGrowth1 evm id s zeroForOne)
  · intro key h0 h1 ha hn h22 _ hk
    exact poolSwapCrossFrame_get f evm id s r zeroForOne key h0 h1 ha hn h22 hk

theorem poolSwapBoundaryFrame_post (f : Frame) (evm : State) (r : PoolSwapResultWords) (tick : UInt256) :
    PoolSwapTickFramePost f (valueLocal f "result" (poolSwapResultValue {r with tick := tick})) evm evm
      {r with tick := tick} := by
  refine ⟨rfl, rfl, store_get_self _ _ _, ?_⟩
  intro key _ _ _ _ _ _ hk
  exact store_get_ne _ _ hk

theorem poolSwapUnchangedFrame_post {f : Frame} (evm : State) {r : PoolSwapResultWords}
    (hr : f.locals.get? "result" = some (poolSwapResultValue r)) : PoolSwapTickFramePost f f evm evm r :=
  ⟨rfl, rfl, hr, fun _ _ _ _ _ _ _ _ => rfl⟩

theorem poolSwapRepriceFrame_post (f : Frame) (evm : State) (r : PoolSwapResultWords) (tick : UInt256) :
    PoolSwapTickFramePost f (poolSwapRepriceFrame f r tick) evm evm {r with tick := tick} := by
  refine ⟨rfl, rfl, store_get_self _ _ _, ?_⟩
  intro key _ _ _ _ _ h23 hk
  exact store_get_ne2 _ _ _ h23 hk

end Benchmarks.UniswapV4PoolManager
