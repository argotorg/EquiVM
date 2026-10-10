import Benchmarks.UniswapV4PoolManager.PoolSwapMemoryFields
import Benchmarks.UniswapV4PoolManager.PoolSwapScanStartTrace
import Benchmarks.UniswapV4PoolManager.TickClampMemory
import Benchmarks.UniswapV4PoolManager.SwapStepStartTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapComputeStoreTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapComputeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

variable {mem : ByteArray} {step state params : UInt256}
  {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}

theorem PoolSwapMemoryView.scan_start (h : PoolSwapMemoryView mem step state params s r p) :
    PoolSwapMemoryView (poolSwapScanStartMemory mem step r.price) step state params
      {s with priceStart := r.price} r p := by
  have hh := h.write_step (s' := {s with priceStart := r.price}) 0 (by decide) r.price rfl
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, uadd_zero_r] at hh
  exact hh

theorem PoolSwapMemoryView.scan_store (h : PoolSwapMemoryView mem step state params s r p)
    (tick : UInt256) (initialized : Bool) :
    PoolSwapMemoryView (tickScanStoreMemory mem step tick initialized) step state params
      {s with tickNext := UInt256.signextend (UInt256.ofNat 2) tick, initialized := initialized} r p := by
  have h1 := h.write_step (s' := {s with initialized := initialized}) 2 (by decide) (UInt256.fromBool initialized) rfl
  exact h1.write_step 1 (by decide) (UInt256.signextend (UInt256.ofNat 2) tick) rfl

theorem PoolSwapMemoryView.clamp_lower (h : PoolSwapMemoryView mem step state params s r p)
    (tick : UInt256) (initialized : Bool) :
    PoolSwapMemoryView (tickClampLowerMemory mem step tick initialized) step state params
      {s with tickNext := tickClampLowerWord tick, initialized := initialized} r p := by
  have hh := h.scan_store tick initialized
  unfold tickClampLowerMemory tickClampLowerWord
  dsimp only
  split
  · exact hh.write_step 1 (by decide) tickMinWord rfl
  · exact hh

theorem PoolSwapMemoryView.clamp (h : PoolSwapMemoryView mem step state params s r p)
    (tick : UInt256) (initialized : Bool) :
    PoolSwapMemoryView (tickClampMemory mem step tick initialized) step state params
      {s with tickNext := tickClampWord tick, initialized := initialized} r p := by
  have hh := h.clamp_lower tick initialized
  unfold tickClampMemory tickClampWord
  dsimp only
  split
  · exact hh.write_step 1 (by decide) tickMaxWord rfl
  · exact hh

theorem PoolSwapMemoryView.compute_start (h : PoolSwapMemoryView mem step state params s r p) (next : UInt256) :
    PoolSwapMemoryView (swapStepStartMemory mem next step ⟨96⟩) step state params
      {s with priceNext := next} r p :=
  h.write_step 3 (by decide) next rfl

theorem PoolSwapMemoryView.compute_store (h : PoolSwapMemoryView mem step state params s r p) (w : SwapStepWords) :
    PoolSwapMemoryView (poolSwapComputeStoreMemory mem step state w) step state params
      (poolSwapComputeStep s s.priceNext w) {r with price := w.next} p := by
  have h1 := h.write_step (s' := {s with feeAmount := w.fee}) 6 (by decide) w.fee rfl
  have h2 := h1.write_step (s' := {s with feeAmount := w.fee, amountOut := w.amountOut}) 5 (by decide) w.amountOut rfl
  have h3 := h2.write_step (s' := poolSwapComputeStep s s.priceNext w) 4 (by decide) w.amountIn rfl
  have h4 := h3.write_result (r' := {r with price := w.next}) 0 (by decide) w.next rfl
  simp only [Nat.mul_zero, show UInt256.ofNat 0 = (⟨0⟩ : UInt256) from rfl, uadd_zero_r] at h4
  exact h4

end Benchmarks.UniswapV4PoolManager
