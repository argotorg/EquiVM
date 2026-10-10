import Benchmarks.UniswapV4PoolManager.TickPriceGuard
import Benchmarks.UniswapV4PoolManager.TickPriceNormalizeTrace
import Benchmarks.UniswapV4PoolManager.TickLogTrace
import Benchmarks.UniswapV4PoolManager.TickPriceFinishTrace
import Benchmarks.UniswapV4PoolManager.MostSignificantBitTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickPriceTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ret sqrtPrice : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 22 ≤ 1024)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hs : sqrtPrice.toNat < 2^160)
    (h : RD (deployedRuntime v) I g s0 ⟨17916⟩ (sqrtPrice :: ret :: R) mem aw rdata σ k C) :
    (tickPriceResult sqrtPrice = none ∧ RDrev (deployedRuntime v) g s0) ∨
    (∃ tick k' C', tickPriceResult sqrtPrice = some tick ∧
      RD (deployedRuntime v) I g s0 ret (tick :: R) mem aw rdata σ k' C') := by
  by_cases hout : tickPriceOutside sqrtPrice
  · have hc : UInt256.gt (tickPriceGuardWord sqrtPrice)
        (UInt256.ofNat 1461446703485210103287273052203988822374428841602) ≠ UInt256.ofNat 0 := by
      have hg : UInt256.gt (tickPriceGuardWord sqrtPrice)
          (UInt256.ofNat 1461446703485210103287273052203988822374428841602) = ⟨1⟩ :=
        ugt_one (tickPriceGuardWord_gt sqrtPrice hout)
      rw [hg]; decide
    have rd1 := poolManagerBlocks.poolManager_block_17916_taken (by simp only [List.length_cons]; omega) hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    have hr := poolManagerBlocks.poolManager_block_18656 (by simp only [List.length_cons]; omega) rd1
    exact .inl ⟨by simp only [tickPriceResult, if_pos hout], hr⟩
  · have hc : UInt256.gt (tickPriceGuardWord sqrtPrice)
        (UInt256.ofNat 1461446703485210103287273052203988822374428841602) = UInt256.ofNat 0 :=
      ugt_zero (tickPriceGuardWord_le sqrtPrice hout)
    have rd1 := poolManagerBlocks.poolManager_block_17916_fallthrough (by simp only [List.length_cons]; omega) hc h
    have rd2 := poolManagerBlocks.poolManager_block_18000 (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [poolManagerBlocks.poolManager_block_18000_stack, tickPriceShiftMask sqrtPrice hs] at rd2
    let price := UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32)
    have hmsb := mostSignificantBitTrace (x := price) v (by simp only [List.length_cons]; omega)
      (by rw [poolManagerPatchedValidJumps v]; jump_dest) rd2
    rcases hmsb with ⟨hz, hr⟩ | ⟨hn, rd3⟩
    · have hz' : UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32) = ⟨0⟩ := hz
      exact .inl ⟨by simp only [tickPriceResult, if_neg hout, if_pos hz'], hr⟩
    · obtain ⟨k4, C4, rd4⟩ := tickPriceNormalizeTrace v (by simp only [List.length_cons]; omega)
        (mostSignificantBit_lt_256 price) rd3
      obtain ⟨k5, C5, rd5⟩ := tickLogTrace v (by simp only [List.length_cons]; omega) rd4
      have hfinish := tickPriceFinishTrace v (by omega) hret hs rd5
      have hn' : UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32) ≠ ⟨0⟩ := hn
      simpa only [tickPriceResult, if_neg hout, if_neg hn'] using hfinish

end Benchmarks.UniswapV4PoolManager
