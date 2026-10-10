import Benchmarks.UniswapV4PoolManager.SwapAfterSource
import Benchmarks.UniswapV4PoolManager.BeforeSwapSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapBeforeStartFrame (f : Frame) : Frame :=
  {f with locals := ((f.locals.insert "beforeSwapDelta" (.int 0)).insert "amountToSwap" (.int 0)).insert "lpFeeOverride" (.int 0)}

def swapBeforeCallFrame (f : Frame) (amount before fee : UInt256) : Frame :=
  {f with locals := f.locals.insert "__c5" (.tuple (beforeSwapReturnValues amount before fee))}

def swapBeforeHookFrame (f : Frame) (amount before fee : UInt256) : Frame :=
  let pair := tupleLocalsFrame (swapBeforeCallFrame f amount before fee) "amountToSwap" "beforeSwapDelta"
    (.int (EVM.signed amount)) (.int (EVM.signed before))
  {pair with locals := pair.locals.insert "lpFeeOverride" (.int (Int.ofNat fee.toNat))}

theorem swapBeforeStartSource (f : Frame) (evm : State) :
    ExecBlock config f evm ((swapTransition.body.drop 15).take 3) (.ok (swapBeforeStartFrame f) evm) :=
  ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
      (execBlock_singleton (ExecStmt.letDecl (by simp only [evalExpr?, pure]))))

theorem swapBeforeAssignSource {f : Frame} {evm : State} {amount before fee : UInt256}
    {oldAmount oldBefore oldFee : Value}
    (ha : f.locals.get? "amountToSwap" = some oldAmount)
    (hb : f.locals.get? "beforeSwapDelta" = some oldBefore)
    (hf : f.locals.get? "lpFeeOverride" = some oldFee) :
    ExecBlock config (swapBeforeCallFrame f amount before fee) evm ((swapTransition.body.drop 19).take 3)
      (.ok (swapBeforeHookFrame f amount before fee) evm) := by
  have hp : ExecBlock config (swapBeforeCallFrame f amount before fee) evm
      ((swapTransition.body.drop 19).take 2)
      (.ok (tupleLocalsFrame (swapBeforeCallFrame f amount before fee) "amountToSwap" "beforeSwapDelta"
        (.int (EVM.signed amount)) (.int (EVM.signed before))) evm) :=
    assignTuplePair (store_get_self _ _ _)
      ((store_get_ne _ _ (by decide : ("__c5" == "amountToSwap") = false)).trans ha)
      ((store_get_ne _ _ (by decide : ("__c5" == "beforeSwapDelta") = false)).trans hb)
      (by decide) (by decide)
  have ht : (tupleLocalsFrame (swapBeforeCallFrame f amount before fee) "amountToSwap" "beforeSwapDelta"
      (.int (EVM.signed amount)) (.int (EVM.signed before))).locals.get? "__c5" =
      some (.tuple (beforeSwapReturnValues amount before fee)) :=
    (store_get_ne2 _ _ _ (by decide : ("amountToSwap" == "__c5") = false)
      (by decide : ("beforeSwapDelta" == "__c5") = false)).trans (store_get_self _ _ _)
  exact execBlock_append hp (execBlock_singleton (ExecStmt.assign
    (evalTupleProjection (evalLocalValue ht) (i := 2) rfl)
    (assignLocalValue ((store_get_ne3 _ _ _ _ (by decide : ("__c5" == "lpFeeOverride") = false)
      (by decide : ("amountToSwap" == "lpFeeOverride") = false)
      (by decide : ("beforeSwapDelta" == "lpFeeOverride") = false)).trans hf))))

end Benchmarks.UniswapV4PoolManager
