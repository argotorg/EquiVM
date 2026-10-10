import Benchmarks.UniswapV4PoolManager.PoolSwapMemory
import Benchmarks.UniswapV4PoolManager.MemoryWindowEq

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

variable {mem : ByteArray} {step state params : UInt256}
  {s : PoolSwapStepWords} {r : PoolSwapResultWords} {p : PoolSwapParamsWords}

theorem PoolSwapMemoryView.window_bound (h : PoolSwapMemoryView mem step state params s r p) :
    min step.toNat state.toNat ≤ mem.size := by
  have hi : step.toNat+256 ≤ mem.size := h.stepFields.inBounds
  have := Nat.min_le_left step.toNat state.toNat
  omega

theorem PoolSwapMemoryView.window_refl (h : PoolSwapMemoryView mem step state params s r p) :
    MemoryWindowEq mem mem 64 (min step.toNat state.toNat) :=
  MemoryWindowEq.refl mem 64 _ h.window_bound

theorem PoolSwapMemoryView.write_step_window (h : PoolSwapMemoryView mem step state params s r p)
    (i : Nat) (hi : i < 8) (word : UInt256) :
    MemoryWindowEq mem (writeWord mem (step+UInt256.ofNat (32*i)).toNat word) 64 (min step.toNat state.toNat) := by
  have hf : step.toNat+256 < UInt256.size := h.stepFields.noWrap
  have hm : step.toNat+256 ≤ mem.size := h.stepFields.inBounds
  have hn := uadd_word_ofNat_toNat step (32*i) (by omega)
  apply MemoryWindowEq.write _ _ _ _ _ h.window_bound
  · rw [hn]; omega
  · left; rw [hn]; have := Nat.min_le_left step.toNat state.toNat; omega

theorem PoolSwapMemoryView.write_result_window (h : PoolSwapMemoryView mem step state params s r p)
    (i : Nat) (hi : i < 3) (word : UInt256) :
    MemoryWindowEq mem (writeWord mem (state+UInt256.ofNat (32*i)).toNat word) 64 (min step.toNat state.toNat) := by
  have hf : state.toNat+96 < UInt256.size := h.resultFields.noWrap
  have hm : state.toNat+96 ≤ mem.size := h.resultFields.inBounds
  have hn := uadd_word_ofNat_toNat state (32*i) (by omega)
  apply MemoryWindowEq.write _ _ _ _ _ h.window_bound
  · rw [hn]; omega
  · left; rw [hn]; have := Nat.min_le_right step.toNat state.toNat; omega

theorem PoolSwapMemoryView.hash_scratch_window (h : PoolSwapMemoryView mem step state params s r p)
    (key base : UInt256) :
    MemoryWindowEq mem (twoWordHashMem key base mem) 64 (min step.toNat state.toNat) := by
  have hm : 64 ≤ mem.size := by
    have hb : step.toNat+256 ≤ mem.size := h.stepFields.inBounds
    omega
  have h1 := MemoryWindowEq.write mem 0 key 64 (min step.toNat state.toNat) h.window_bound (by omega) (.inr (by decide))
  have h2 := MemoryWindowEq.write (writeWord mem 0 key) 32 base 64 (min step.toNat state.toNat)
    (by rw [h1.size]; exact h.window_bound) (by rw [h1.size]; exact hm) (.inr (by decide))
  exact h1.trans h2

end Benchmarks.UniswapV4PoolManager
