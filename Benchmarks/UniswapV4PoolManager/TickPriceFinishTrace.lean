import Benchmarks.UniswapV4PoolManager.TickPriceSelectTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickPriceFinishTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret sqrtPrice log2 : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 12 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : sqrtPrice.toNat < 2^160)
    (h : RD (deployedRuntime v) I g s0 ⟨18536⟩
      (UInt256.ofNat 2 :: tickPriceLowRaw log2 :: tickPriceScaled log2 :: sqrtPrice :: ret :: R) mem aw rdata σ k C) :
    (tickPriceFinish sqrtPrice log2 = none ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ tick k' C', tickPriceFinish sqrtPrice log2 = some tick ∧
      RD (deployedRuntime v) I g s0 ret (tick :: R) mem aw rdata σ k' C') := by
  have hhigh : UInt256.signextend (UInt256.ofNat 2)
      (UInt256.sar (UInt256.ofNat 128) (UInt256.ofNat 291339464771989622907027621153398088495 + tickPriceScaled log2)) =
        tickPriceHigh log2 := by rw [u256_add_comm]; rfl
  by_cases heq : tickPriceLow log2 = tickPriceHigh log2
  · have hc : UInt256.eq ⟨0⟩ (UInt256.eq
        (UInt256.signextend (UInt256.ofNat 2) (tickPriceLowRaw log2))
        (UInt256.signextend (UInt256.ofNat 2) (UInt256.sar (UInt256.ofNat 128)
          (UInt256.ofNat 291339464771989622907027621153398088495 + tickPriceScaled log2)))) = UInt256.ofNat 0 := by
      rw [hhigh]
      change UInt256.eq ⟨0⟩ (UInt256.eq (tickPriceLow log2) (tickPriceHigh log2)) = _
      rw [heq, u256_eq_refl]
      decide
    have rd1 := poolManagerBlocks.poolManager_block_18536_fallthrough (by simp only [List.length_cons]; omega) hc h
    simp only [poolManagerBlocks.poolManager_block_18536_fallthrough_stack, hhigh] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_18572 (by omega) hret rd1
    exact .inr ⟨tickPriceLow log2, _, _, by simp only [tickPriceFinish, tickPriceChoose, if_pos heq], rd2⟩
  · have hc : UInt256.eq ⟨0⟩ (UInt256.eq
        (UInt256.signextend (UInt256.ofNat 2) (tickPriceLowRaw log2))
        (UInt256.signextend (UInt256.ofNat 2) (UInt256.sar (UInt256.ofNat 128)
          (UInt256.ofNat 291339464771989622907027621153398088495 + tickPriceScaled log2)))) ≠ UInt256.ofNat 0 := by
      rw [hhigh]
      change UInt256.eq ⟨0⟩ (UInt256.eq (tickPriceLow log2) (tickPriceHigh log2)) ≠ _
      rw [u256_eq_of_ne heq]
      decide
    have rd1 := poolManagerBlocks.poolManager_block_18536_taken (by simp only [List.length_cons]; omega) hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_18536_taken_stack, hhigh] at rd1
    exact tickPriceSelectTrace v hstack hret hs
      ((signextend24_eq_iff _).mpr (signextend24_canonical _)) heq rd1

end Benchmarks.UniswapV4PoolManager
