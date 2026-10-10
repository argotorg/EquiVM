import Benchmarks.UniswapV4PoolManager.AfterSwapCall
import Benchmarks.UniswapV4PoolManager.TupleLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def swapAfterStartFrame (f : Frame) : Frame := {f with locals := f.locals.insert "hookDelta" (.int 0)}

def swapAfterCallFrame (f : Frame) (delta hook : UInt256) : Frame :=
  {f with locals := f.locals.insert "__c7" (.tuple [.int (EVM.signed delta), .int (EVM.signed hook)])}

def swapAfterHookFrame (f : Frame) (delta hook : UInt256) : Frame :=
  tupleLocalsFrame (swapAfterCallFrame f delta hook) "swapDelta" "hookDelta"
    (.int (EVM.signed delta)) (.int (EVM.signed hook))

theorem swapAfterAssignSource {f : Frame} {evm : State} {delta hook : UInt256} {oldDelta oldHook : Value}
    (hd : f.locals.get? "swapDelta" = some oldDelta)
    (hh : f.locals.get? "hookDelta" = some oldHook) :
    ExecBlock config (swapAfterCallFrame f delta hook) evm ((swapTransition.body.drop 27).take 2)
      (.ok (swapAfterHookFrame f delta hook) evm) :=
  assignTuplePair (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("__c7" == "swapDelta") = false)).trans hd)
    ((store_get_ne _ _ (by decide : ("__c7" == "hookDelta") = false)).trans hh)
    (by decide) (by decide)

end Benchmarks.UniswapV4PoolManager
