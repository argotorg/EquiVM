import Benchmarks.UniswapV4PoolManager.PoolSwapMemoryWindow
import Benchmarks.UniswapV4PoolManager.PoolSwapComputeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

variable {mem : ByteArray} {step state params : UInt256}
  {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}

theorem PoolSwapMemoryView.scan_start_window (h : PoolSwapMemoryView mem step state params s r p) :
    MemoryWindowEq mem (poolSwapScanStartMemory mem step r.price) 64 (min step.toNat state.toNat) := by
  have hh := h.write_step_window 0 (by decide) r.price
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, uadd_zero_r] at hh
  exact hh

theorem PoolSwapMemoryView.scan_store_window (h : PoolSwapMemoryView mem step state params s r p)
    (tick : UInt256) (initialized : Bool) :
    MemoryWindowEq mem (tickScanStoreMemory mem step tick initialized) 64 (min step.toNat state.toNat) := by
  have h1 := h.write_step (s' := {s with initialized := initialized}) 2 (by decide) (UInt256.fromBool initialized) rfl
  exact (h.write_step_window 2 (by decide) (UInt256.fromBool initialized)).trans
    (h1.write_step_window 1 (by decide) (UInt256.signextend (UInt256.ofNat 2) tick))

theorem PoolSwapMemoryView.clamp_lower_window (h : PoolSwapMemoryView mem step state params s r p)
    (tick : UInt256) (initialized : Bool) :
    MemoryWindowEq mem (tickClampLowerMemory mem step tick initialized) 64 (min step.toNat state.toNat) := by
  have hh := h.scan_store_window tick initialized
  unfold tickClampLowerMemory
  dsimp only
  split
  · exact hh.trans ((h.scan_store tick initialized).write_step_window 1 (by decide) tickMinWord)
  · exact hh

theorem PoolSwapMemoryView.clamp_window (h : PoolSwapMemoryView mem step state params s r p)
    (tick : UInt256) (initialized : Bool) :
    MemoryWindowEq mem (tickClampMemory mem step tick initialized) 64 (min step.toNat state.toNat) := by
  have hh := h.clamp_lower_window tick initialized
  unfold tickClampMemory
  dsimp only
  split
  · exact hh.trans ((h.clamp_lower tick initialized).write_step_window 1 (by decide) tickMaxWord)
  · exact hh

theorem PoolSwapMemoryView.compute_start_window (h : PoolSwapMemoryView mem step state params s r p) (next : UInt256) :
    MemoryWindowEq mem (swapStepStartMemory mem next step ⟨96⟩) 64 (min step.toNat state.toNat) :=
  h.write_step_window 3 (by decide) next

theorem PoolSwapMemoryView.compute_store_window (h : PoolSwapMemoryView mem step state params s r p) (w : SwapStepWords) :
    MemoryWindowEq mem (poolSwapComputeStoreMemory mem step state w) 64 (min step.toNat state.toNat) := by
  have h1 := h.write_step (s' := {s with feeAmount := w.fee}) 6 (by decide) w.fee rfl
  have h2 := h1.write_step (s' := {s with feeAmount := w.fee, amountOut := w.amountOut}) 5 (by decide) w.amountOut rfl
  have h3 := h2.write_step (s' := poolSwapComputeStep s s.priceNext w) 4 (by decide) w.amountIn rfl
  have hw3 := ((h.write_step_window 6 (by decide) w.fee).trans
    (h1.write_step_window 5 (by decide) w.amountOut)).trans (h2.write_step_window 4 (by decide) w.amountIn)
  have hw4 := h3.write_result_window 0 (by decide) w.next
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, uadd_zero_r] at hw4
  exact hw3.trans hw4

end Benchmarks.UniswapV4PoolManager
