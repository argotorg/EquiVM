import Benchmarks.UniswapV4PoolManager.PoolSwapMemoryFields
import Benchmarks.UniswapV4PoolManager.PoolSwapFeeTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapTickTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapTickWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

variable {mem : ByteArray} {step state params : UInt256}
  {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}

theorem PoolSwapMemoryView.protocol (h : PoolSwapMemoryView mem step state params s r p) (fee protocol : UInt256) :
    PoolSwapMemoryView (poolSwapProtocolMemory mem step s fee protocol) step state params
      (poolSwapProtocolStep s fee protocol) r p := by
  unfold poolSwapProtocolMemory poolSwapProtocolStep
  split
  · exact h
  · exact h.write_step 6 (by decide) _ rfl

theorem PoolSwapMemoryView.growth_step (h : PoolSwapMemoryView mem step state params s r p) :
    PoolSwapMemoryView (poolSwapGrowthMemory mem step s r.liquidity) step state params
      (poolSwapGrowthStep s r.liquidity) r p := by
  by_cases hz : r.liquidity = ⟨0⟩
  · simpa only [poolSwapGrowthMemory, poolSwapGrowthStep, if_pos hz] using h
  · simp only [poolSwapGrowthMemory, poolSwapGrowthStep, if_neg hz]
    exact h.write_step 7 (by decide) _ rfl

theorem PoolSwapMemoryView.cross_hash (h : PoolSwapMemoryView mem step state params s r p) (id : UInt256) :
    PoolSwapMemoryView (tickCrossMemory mem id s.tickNext) step state params s r p :=
  h.hash_scratch _ _

theorem PoolSwapMemoryView.cross (h : PoolSwapMemoryView mem step state params s r p)
    (evm : State) (id : UInt256) (zeroForOne : Bool) :
    PoolSwapMemoryView (poolSwapCrossMemory mem id state s evm zeroForOne r.liquidity) step state params
      s {r with liquidity := poolSwapCrossLiquidity evm id s zeroForOne r.liquidity} p :=
  (h.cross_hash id).write_result 2 (by decide) _ rfl

theorem PoolSwapMemoryView.tick_update (h : PoolSwapMemoryView mem step state params s r p)
    (evm : State) (id : UInt256) (zeroForOne : Bool) :
    PoolSwapMemoryView (poolSwapTickMemory mem id state evm s r zeroForOne) step state params
      s (poolSwapTickResultWords evm id s r zeroForOne) p := by
  unfold poolSwapTickMemory poolSwapTickResultWords
  by_cases he : r.price = s.priceNext
  · simp only [if_pos he]
    by_cases hi : s.initialized = true
    · simp only [if_pos hi]
      exact (h.cross evm id zeroForOne).write_result 1 (by decide) _ rfl
    · simp only [if_neg hi]
      exact h.write_result 1 (by decide) _ rfl
  · simp only [if_neg he]
    by_cases hs : r.price = s.priceStart
    · simpa only [if_pos hs] using h
    · simp only [if_neg hs]
      cases tickPriceResult r.price with
      | none => exact h
      | some tick => exact h.write_result 1 (by decide) tick rfl

end Benchmarks.UniswapV4PoolManager
