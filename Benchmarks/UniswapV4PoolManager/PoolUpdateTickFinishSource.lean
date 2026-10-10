import Benchmarks.UniswapV4PoolManager.PoolUpdateTickTail

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickFeesPost (evm : EVM.State) (id packed : UInt256) (tick : Int) : EVM.State :=
  if tickFeesNeeded evm id tick (Int.ofNat (tickGrossWord packed).toNat) then tickFeeWrites evm id tick else evm
def poolUpdateTickFinishResult (f : Frame) (evm : EVM.State) (id packed gross : UInt256)
    (tick delta : Int) (upper flipped : Bool) : ExecResult :=
  if tickFeesNeeded evm id tick (Int.ofNat (tickGrossWord packed).toNat) ∧ evm.executionEnv.perm = false then
    .staticViolation else
    poolUpdateTickTailResult f (tickFeesPost evm id packed tick) id packed gross tick delta upper flipped

theorem poolUpdateTickFinishSource {f : Frame} {evm : EVM.State} {id packed gross : UInt256}
    {tick delta : Int} {upper flipped : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hi : f.locals.get? "info" = some (tickRefValue id tick))
    (ht : f.locals.get? "tick" = some (.int tick))
    (hb : f.locals.get? "liquidityNetBefore" = some (.int (EVM.signed (tickNetWord packed))))
    (hd : f.locals.get? "liquidityDelta" = some (.int delta))
    (hu : f.locals.get? "upper" = some (.bool upper))
    (hg : f.locals.get? "liquidityGrossAfter" = some (.int (Int.ofNat gross.toNat)))
    (hgb : f.locals.get? "liquidityGrossBefore" = some (.int (Int.ofNat (tickGrossWord packed).toNat)))
    (hflip : f.locals.get? "flipped" = some (.bool flipped)) :
    ∃ f', ExecFuncBody config f evm (poolUpdateTickFunction.body.drop 9)
      (poolUpdateTickFinishResult f' evm id packed gross tick delta upper flipped) := by
  have hfees := poolUpdateTickFees (evm := evm) hf hs hi ht hgb
  by_cases hstop : tickFeesNeeded evm id tick (Int.ofNat (tickGrossWord packed).toNat) ∧ evm.executionEnv.perm = false
  · simp only [tickFeeResult, if_pos hstop.1, if_pos hstop.2] at hfees
    exact ⟨f, by simpa only [poolUpdateTickFinishResult, if_pos hstop] using
      (ExecFuncBody.execBlockStatic (ExecBlock.consStatic hfees) :
        ExecFuncBody config f evm (poolUpdateTickFunction.body.drop 9) .staticViolation)⟩
  · let f1 := tickFeeFrame f evm id (Int.ofNat (tickGrossWord packed).toNat)
    have hfeesOk : ExecStmt config f evm poolUpdateTickFunction.body[9]!
        (.ok f1 (tickFeesPost evm id packed tick)) := by
      by_cases hn : tickFeesNeeded evm id tick (Int.ofNat (tickGrossWord packed).toNat)
      · have hp : ¬evm.executionEnv.perm = false := fun hp => hstop ⟨hn, hp⟩
        simpa only [tickFeeResult, tickFeesPost, if_pos hn, if_neg hp] using hfees
      · simpa only [tickFeeResult, tickFeesPost, if_neg hn] using hfees
    obtain ⟨f', htail⟩ := poolUpdateTickTail (f := f1) (evm := tickFeesPost evm id packed tick)
      ((tickFeeFrame_get (by decide : ("__c1" == "info") = false)).trans hi)
      ((tickFeeFrame_get (by decide : ("__c1" == "liquidityNetBefore") = false)).trans hb)
      ((tickFeeFrame_get (by decide : ("__c1" == "liquidityDelta") = false)).trans hd)
      ((tickFeeFrame_get (by decide : ("__c1" == "upper") = false)).trans hu)
      ((tickFeeFrame_get (by decide : ("__c1" == "liquidityGrossAfter") = false)).trans hg)
      ((tickFeeFrame_get (by decide : ("__c1" == "flipped") = false)).trans hflip)
    refine ⟨f', ?_⟩
    simp only [poolUpdateTickFinishResult, if_neg hstop]
    exact execFuncBody_prepend (execBlock_singleton hfeesOk) htail

end Benchmarks.UniswapV4PoolManager
