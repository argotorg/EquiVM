import Benchmarks.UniswapV3.Pool.WordArrayMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: the first struct allocation leaves the solc zero word untouched.
theorem wordArrayAllocMem_fresh_read96 (ws : List UInt256) (hn : ws ≠ []) :
    (wordArrayAllocMem solcFreePtrMem ⟨128⟩ ws).readWithPadding 96 32 =
      (⟨0⟩ : UInt256).toByteArray := by
  cases ws with
  | nil => exact False.elim (hn rfl)
  | cons w ws =>
    let base := writeWord solcFreePtrMem 64 (⟨128⟩ + UInt256.ofNat (32 * (w :: ws).length))
    have hb : base.size = 96 := by
      dsimp only [base]
      rw [writeWord_sparse_size, solcFreePtrMem_size]
      rfl
    change (writeWordArray (writeWord base 128 w) 160 ws).readWithPadding 96 32 = _
    rw [writeWordArray_preserve_below _ _ _ _ (by decide)
      (by rw [writeWord_sparse_size]; omega)]
    have h := writeWord_read_gap32 base w
    rw [hb] at h
    exact h

theorem wordArrayAllocMem_fresh_zero (ws : List UInt256) (hn : ws ≠ []) :
    memLoad (UInt256.ofNat 96) (wordArrayAllocMem solcFreePtrMem ⟨128⟩ ws) = ⟨0⟩ := by
  apply mloadWordValue_of_readWithPadding
  · rw [wordArrayAllocMem_size _ _ _ (by decide) hn]
    change 96 < max _ (128 + 32 * ws.length)
    omega
  · exact wordArrayAllocMem_fresh_read96 ws hn

end Benchmarks.UniswapV3.Pool
