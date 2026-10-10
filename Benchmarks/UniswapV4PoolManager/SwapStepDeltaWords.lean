import Benchmarks.UniswapV4PoolManager.Amount0Words
import Benchmarks.UniswapV4PoolManager.Amount1Words

open Ethereum Ethereum.EVM Reasoning.Theory
namespace Benchmarks.UniswapV4PoolManager

def amountDeltaFits (a b liquidity : UInt256) (use0 roundUp : Bool) : Prop :=
  if use0 then amount0Fits a b liquidity roundUp else amount1Fits a b liquidity
instance (a b liquidity : UInt256) (use0 roundUp : Bool) :
    Decidable (amountDeltaFits a b liquidity use0 roundUp) := by
  unfold amountDeltaFits
  infer_instance
def amountDeltaWord (a b liquidity : UInt256) (use0 roundUp : Bool) : UInt256 :=
  if use0 then amount0Word a b liquidity roundUp else amount1Word a b liquidity roundUp

def swapStepDeltaFits (price next liquidity : UInt256) (input zeroForOne : Bool) : Prop :=
  if zeroForOne then amountDeltaFits next price liquidity input input
  else amountDeltaFits price next liquidity (!input) input
instance (price next liquidity : UInt256) (input zeroForOne : Bool) :
    Decidable (swapStepDeltaFits price next liquidity input zeroForOne) := by
  unfold swapStepDeltaFits
  infer_instance
def swapStepDeltaWord (price next liquidity : UInt256) (input zeroForOne : Bool) : UInt256 :=
  if zeroForOne then amountDeltaWord next price liquidity input input
  else amountDeltaWord price next liquidity (!input) input

end Benchmarks.UniswapV4PoolManager
