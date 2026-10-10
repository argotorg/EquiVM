import Benchmarks.UniswapV4PoolManager.FunctionResultTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: finishing a block preserves an already terminal function trace.
theorem functionResultTrace_finishBlock {code : ByteArray} {g : Sat256} {s0 : State}
    {onReturn : State → Option (List Value) → Prop} {result : ExecResult}
    (h : functionResultTrace code g s0 onReturn result) :
    functionResultTrace code g s0 onReturn (finishBlockResult result) := by
  cases result with
  | returned | reverted | staticViolation => exact h
  | ok | «break» | «continue» => exact False.elim h

end Benchmarks.UniswapV4PoolManager
