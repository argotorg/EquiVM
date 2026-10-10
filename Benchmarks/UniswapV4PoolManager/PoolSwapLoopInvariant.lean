import Benchmarks.UniswapV4PoolManager.PoolSwapIterationPost
import Benchmarks.UniswapV4PoolManager.PoolSwapIterationTrace
import Benchmarks.UniswapV4PoolManager.Signed24Bounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

structure PoolSwapLoopWords where
  step : PoolSwapStepWords
  result : PoolSwapResultWords
  remaining : UInt256
  calculated : UInt256
  amountToProtocol : UInt256

def poolSwapLoopStack (q : PoolSwapLoopWords) (p : PoolSwapParamsWords)
    (id step state params x1 tag fee protocol : UInt256) (R : List UInt256) : List UInt256 :=
  [q.remaining, x1, params, q.calculated, tag, fee, protocol, q.amountToProtocol,
    UInt256.fromBool (!p.zeroForOne), step, poolSlot id, state] ++ R

structure PoolSwapLoopInvariant (f : Frame) (mem : ByteArray)
    (id step state params fee protocol : UInt256) (p : PoolSwapParamsWords) (q : PoolSwapLoopWords) : Prop where
  locals : PoolSwapLoopLocals f id q.step q.result p q.remaining q.calculated fee protocol q.amountToProtocol
  memory : PoolSwapMemoryView mem step state params q.step q.result p
  price : q.result.price.toNat < 2^160
  tick : int24Canonical q.result.tick
  liquidity : q.result.liquidity.toNat < 2^128

end Benchmarks.UniswapV4PoolManager
