import Benchmarks.Midnight.MarketStoreSource
import Benchmarks.Midnight.TouchMarketSourceBase

/-! Call the deployment helper and emit the newly initialized market. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def marketCreatedFrame (frame : Frame) (addr : AccountAddress) : Frame :=
  resumeAfterInternalCall frame "__c2" (some [.address addr])

theorem marketStoreCallReturn {frame : Frame} {evm evm' : EVM.State} {m : MarketData}
    {calleeFrame : Frame} {addr : AccountAddress}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hbody : ExecFuncBody config (touchMarketCallFrame frame.immutables m) evm
      marketStoreCodeFunction.body (.returned calleeFrame evm' (some [.address addr]))) :
    ExecStmt config frame evm (.internalCall "IdLib_storeInCode" [.var "market"] "__c2")
      (.ok (marketCreatedFrame frame addr) evm') := by
  apply internalCallFunctionReturn (callee := marketStoreCodeFunction)
    (locals := touchMarketArguments m) (argVals := [Model.marketValue m.value])
  · simp only [evalExprs?, evalExpr?, hm, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · rw [hc]; rfl
  · rfl
  · simpa only [hc] using hbody

theorem marketStoreCallRevert {frame : Frame} {evm : EVM.State} {m : MarketData}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hbody : ExecFuncBody config (touchMarketCallFrame frame.immutables m) evm
      marketStoreCodeFunction.body .reverted) :
    ExecBlock config frame evm (touchMarketInitBody.drop 18) .reverted := by
  apply ExecBlock.consRevert
  apply internalCallFunctionRevert (callee := marketStoreCodeFunction)
    (locals := touchMarketArguments m) (argVals := [Model.marketValue m.value])
  · simp only [evalExprs?, evalExpr?, hm, EvalResult.ofOption, pure, bind, EvalResult.bind]
  · rw [hc]; rfl
  · rfl
  · simpa only [hc] using hbody

theorem marketCreatedSource {frame : Frame} {evm evm' : EVM.State} {m : MarketData}
    {calleeFrame : Frame} {addr : AccountAddress} {id : UInt256}
    (hc : frame.contract = contract)
    (hm : frame.locals.get? "market" = some (Model.marketValue m.value))
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hperm : evm'.executionEnv.perm = true)
    (hbody : ExecFuncBody config (touchMarketCallFrame frame.immutables m) evm
      marketStoreCodeFunction.body (.returned calleeFrame evm' (some [.address addr]))) :
    ExecBlock config frame evm (touchMarketInitBody.drop 18)
      (.ok (marketCreatedFrame frame addr) evm') := by
  refine ExecBlock.consNormal (marketStoreCallReturn hc hm hbody) ?_
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [Model.marketValue m.value,
    wordBytes32Value id]) hperm ?_) ExecBlock.nil
  simp only [evalExprs?, evalExpr?, marketCreatedFrame, resumeAfterInternalCall,
    store_get_ne _ _ (show ("__c2" == "market") = false from rfl),
    store_get_ne _ _ (show ("__c2" == "id") = false from rfl), hm, hid,
    EvalResult.ofOption, bind, EvalResult.bind, pure]

end Benchmarks.Midnight
