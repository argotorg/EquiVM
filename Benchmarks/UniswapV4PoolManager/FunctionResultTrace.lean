import Benchmarks.UniswapV4PoolManager.CallComposition
import Reasoning.Dispatch

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: relate a source function result to an arbitrary return continuation.
def functionResultTrace (fork : Ethereum.Fork) (code : ByteArray) (g : Sat256) (s0 : State)
    (onReturn : State → Option (List Value) → Prop) : ExecResult → Prop
  | .returned _ evm values => onReturn evm values
  | .reverted => RDrev fork code g s0
  | .staticViolation => RDstatic fork code g s0
  | _ => False

-- LIBRARY CANDIDATE: transform a successful function continuation while preserving failures.
theorem functionResultTrace_mono {code : ByteArray} {g : Sat256} {s0 : State}
    {before after : State → Option (List Value) → Prop} {result : ExecResult}
    (hr : functionResultTrace fork code g s0 before result)
    (hn : ∀ post values, before post values → after post values) :
    functionResultTrace fork code g s0 after result := by
  cases result with
  | returned _ post values => exact hn post values hr
  | reverted | staticViolation => exact hr
  | ok | «break» | «continue» | noMatch | decodingFailed => exact False.elim hr

end Benchmarks.UniswapV4PoolManager
