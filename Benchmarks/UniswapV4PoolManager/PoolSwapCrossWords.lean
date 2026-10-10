import Benchmarks.UniswapV4PoolManager.PoolSwapStepWords
import Benchmarks.UniswapV4PoolManager.PoolFeeGrowthStorage
import Benchmarks.UniswapV4PoolManager.TickCrossWords
import Benchmarks.UniswapV4PoolManager.LiquidityAddWords
import Benchmarks.UniswapV4PoolManager.SignedNormalizeRange
import Benchmarks.UniswapV4PoolManager.WordSignextend128

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

def poolSwapCrossGrowth0 (evm : State) (id : UInt256) (s : PoolSwapStepWords) (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then s.feeGrowthGlobal else poolFeeGrowthWord evm id false

def poolSwapCrossGrowth1 (evm : State) (id : UInt256) (s : PoolSwapStepWords) (zeroForOne : Bool) : UInt256 :=
  if zeroForOne then poolFeeGrowthWord evm id true else s.feeGrowthGlobal

def poolSwapCrossDelta (zeroForOne : Bool) (net : UInt256) : UInt256 :=
  if zeroForOne then UInt256.signextend (UInt256.ofNat 15) (UInt256.sub ⟨0⟩ net) else net

theorem poolSwapCrossDelta_fits (zeroForOne : Bool) {net : UInt256}
    (hn : signedFits ⟨128, by decide⟩ (EVM.signed net)) :
    signedFits ⟨128, by decide⟩ (EVM.signed (poolSwapCrossDelta zeroForOne net)) := by
  cases zeroForOne
  · exact hn
  · change signedFits ⟨128, by decide⟩ (EVM.signed (UInt256.signextend (UInt256.ofNat 15) (UInt256.sub ⟨0⟩ net)))
    rw [← normalizeSigned128Word]
    exact normalizeSigned_fits _ _

def poolSwapCrossPost (evm : State) (id : UInt256) (s : PoolSwapStepWords) (zeroForOne : Bool) : State :=
  tickCrossPost evm id (EVM.signed s.tickNext)
    (poolSwapCrossGrowth0 evm id s zeroForOne) (poolSwapCrossGrowth1 evm id s zeroForOne)

def poolSwapCrossNet (evm : State) (id : UInt256) (s : PoolSwapStepWords) (zeroForOne : Bool) : UInt256 :=
  tickCrossNet evm id (EVM.signed s.tickNext)
    (poolSwapCrossGrowth0 evm id s zeroForOne) (poolSwapCrossGrowth1 evm id s zeroForOne)

def poolSwapCrossLiquidity (evm : State) (id : UInt256) (s : PoolSwapStepWords) (zeroForOne : Bool)
    (liquidity : UInt256) : UInt256 :=
  liquidityAddResultWord liquidity (EVM.signed (poolSwapCrossDelta zeroForOne (poolSwapCrossNet evm id s zeroForOne)))

end Benchmarks.UniswapV4PoolManager
