import Benchmarks.UniswapV4PoolManager.PoolSwapMemoryWindow
import Benchmarks.UniswapV4PoolManager.PoolSwapAccountingTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

variable {mem : ByteArray} {step state params : UInt256}
  {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}

theorem PoolSwapMemoryView.protocol_window (h : PoolSwapMemoryView mem step state params s r p) (fee protocol : UInt256) :
    MemoryWindowEq mem (poolSwapProtocolMemory mem step s fee protocol) 64 (min step.toNat state.toNat) := by
  unfold poolSwapProtocolMemory
  split
  · exact h.window_refl
  · exact h.write_step_window 6 (by decide) _

theorem PoolSwapMemoryView.growth_window (h : PoolSwapMemoryView mem step state params s r p) :
    MemoryWindowEq mem (poolSwapGrowthMemory mem step s r.liquidity) 64 (min step.toNat state.toNat) := by
  unfold poolSwapGrowthMemory
  split
  · exact h.window_refl
  · exact h.write_step_window 7 (by decide) _

theorem PoolSwapMemoryView.cross_window (h : PoolSwapMemoryView mem step state params s r p)
    (evm : State) (id : UInt256) (zeroForOne : Bool) :
    MemoryWindowEq mem (poolSwapCrossMemory mem id state s evm zeroForOne r.liquidity) 64 (min step.toNat state.toNat) :=
  (h.hash_scratch_window (UInt256.signextend (UInt256.ofNat 2) s.tickNext) (poolSlot id+UInt256.ofNat 4)).trans
    ((h.cross_hash id).write_result_window 2 (by decide) _)

theorem PoolSwapMemoryView.tick_update_window (h : PoolSwapMemoryView mem step state params s r p)
    (evm : State) (id : UInt256) (zeroForOne : Bool) :
    MemoryWindowEq mem (poolSwapTickMemory mem id state evm s r zeroForOne) 64 (min step.toNat state.toNat) := by
  unfold poolSwapTickMemory
  by_cases he : r.price = s.priceNext
  · rw [if_pos he]
    by_cases hi : s.initialized = true
    · rw [if_pos hi]
      exact (h.cross_window evm id zeroForOne).trans
        ((h.cross evm id zeroForOne).write_result_window 1 (by decide) _)
    · rw [if_neg hi]
      exact h.write_result_window 1 (by decide) _
  · rw [if_neg he]
    split
    · exact h.window_refl
    · cases tickPriceResult r.price with
      | none => exact h.window_refl
      | some tick => exact h.write_result_window 1 (by decide) tick

theorem PoolSwapMemoryView.accounting_window (h : PoolSwapMemoryView mem step state params s r p)
    (evm : State) (id fee protocol : UInt256) :
    MemoryWindowEq mem (poolSwapAccountingMemory mem step state id evm s r fee protocol p.zeroForOne)
      64 (min step.toNat state.toNat) :=
  ((h.protocol_window fee protocol).trans ((h.protocol fee protocol).growth_window)).trans
    (((h.protocol fee protocol).growth_step).tick_update_window evm id p.zeroForOne)

end Benchmarks.UniswapV4PoolManager
