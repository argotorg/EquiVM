import Benchmarks.UniswapV4PoolManager.AfterLiquidityCall
import Benchmarks.UniswapV4PoolManager.TupleLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def modifyLiquidityAfterCallFrame (f : Frame) (caller hookDelta : UInt256) : Frame :=
  {f with locals := f.locals.insert "__c8" (.tuple [.int (EVM.signed caller), .int (EVM.signed hookDelta)])}

def modifyLiquidityAfterHookFrame (f : Frame) (caller hookDelta : UInt256) : Frame :=
  {f with locals := ((modifyLiquidityAfterCallFrame f caller hookDelta).locals.insert
    "callerDelta" (.int (EVM.signed caller))).insert "hookDelta" (.int (EVM.signed hookDelta))}

theorem modifyLiquidityAfterHookFrame_contract (f : Frame) (caller hookDelta : UInt256) :
    (modifyLiquidityAfterHookFrame f caller hookDelta).contract = f.contract := rfl

theorem modifyLiquidityAfterAssignSource {f : Frame} {evm : State} {caller hookDelta : UInt256}
    {oldCaller oldHook : Value}
    (hc : f.locals.get? "callerDelta" = some oldCaller)
    (hh : f.locals.get? "hookDelta" = some oldHook) :
    ExecBlock config (modifyLiquidityAfterCallFrame f caller hookDelta) evm
      ((modifyLiquidityTransition.body.drop 27).take 2)
      (.ok (modifyLiquidityAfterHookFrame f caller hookDelta) evm) :=
  assignTuplePair (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("__c8" == "callerDelta") = false)).trans hc)
    ((store_get_ne _ _ (by decide : ("__c8" == "hookDelta") = false)).trans hh)
    (by decide) (by decide)

end Benchmarks.UniswapV4PoolManager
