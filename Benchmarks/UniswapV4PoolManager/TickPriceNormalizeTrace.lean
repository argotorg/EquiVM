import Benchmarks.UniswapV4PoolManager.TickLogCompiled
import Benchmarks.UniswapV4PoolManager.Routines
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_051
import Benchmarks.UniswapV4PoolManager.RuntimeBlocks_052

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickPriceNormalizeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw price msb : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length + 7 ≤ 1024) (hm : msb.toNat < 256)
    (h : RD (deployedRuntime v) I g s0 ⟨18041⟩
      (msb :: UInt256.ofNat 255 :: price :: price :: R) mem aw rdata σ k C) :
    ∃ k' C', RD (deployedRuntime v) I g s0 ⟨18089⟩
      (tickPriceNormalize price msb :: msb :: R) mem aw rdata σ k' C' := by
  have hclean : UInt256.land msb (UInt256.ofNat 255) = msb :=
    u256LandMaskCleanOfToNat msb _ (bits := 8) rfl hm
  by_cases hh : 128 ≤ msb.toNat
  · have hc : UInt256.lt (UInt256.land msb (UInt256.ofNat 255)) (UInt256.ofNat 128) = UInt256.ofNat 0 := by
      rw [hclean]; exact ult_zero hh
    have rd1 := poolManagerBlocks.poolManager_block_18041_fallthrough (by omega) hc h
    simp only [poolManagerBlocks.poolManager_block_18041_fallthrough_stack, hclean] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_18052 (by omega) rd1
    simp only [poolManagerBlocks.poolManager_block_18052_stack] at rd2
    have hsub : msb + UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007913129639809 =
        UInt256.sub msb (UInt256.ofNat 127) := wordAddNegSub msb (UInt256.ofNat 127)
    rw [hsub] at rd2
    simp only [tickPriceNormalize, if_pos hh]
    exact ⟨_, _, rd2⟩
  · have hc : UInt256.lt (UInt256.land msb (UInt256.ofNat 255)) (UInt256.ofNat 128) ≠ UInt256.ofNat 0 := by
      rw [hclean]
      have hc' : UInt256.lt msb (UInt256.ofNat 128) = ⟨1⟩ := ult_one (by change msb.toNat < 128; omega)
      rw [hc']; decide
    have rd1 := poolManagerBlocks.poolManager_block_18041_taken (by omega) hc
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) h
    simp only [poolManagerBlocks.poolManager_block_18041_taken_stack, hclean] at rd1
    have rd2 := poolManagerBlocks.poolManager_block_18644 (by omega)
      (by rw [poolManagerPatchedValidJumpsRuntime v]; jump_dest) rd1
    simp only [tickPriceNormalize, if_neg hh]
    exact ⟨_, _, rd2⟩

end Benchmarks.UniswapV4PoolManager
