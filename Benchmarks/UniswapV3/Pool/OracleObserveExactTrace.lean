import Benchmarks.UniswapV3.Pool.ObservationCoverage
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveExactX (afterSide : Bool)
    {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State} {k C : Nat}
    {aw free beforePtr afterPtr targetRaw z0 z1 : UInt256} {obs : OracleObservation}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 (if afterSide then ⟨13450⟩ else ⟨13410⟩)
      (afterPtr :: beforePtr :: targetRaw :: z0 :: z1 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hb : free.toNat ≤ 2 ^ 200)
    (hobs : ObservationMemory mem (if afterSide then afterPtr else beforePtr) obs)
    (hend : (if afterSide then afterPtr else beforePtr).toNat + 128 ≤ free.toNat)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 8 ≤ 1024) :
    RD (deployedRuntime v) ee g s0 ⟨13584⟩
      (obs.secondsPerLiquidity :: EVM.wordOfInt obs.tickCumulative :: R)
      mem aw rdata σ (k + 17) (C + 51) := by
  have hbound : (if afterSide then afterPtr else beforePtr).toNat + 128 < UInt256.size := by
    change _ < 2 ^ 256
    omega
  have ht := hobs.load_tick hbound
  have hs := hobs.load_seconds hbound
  obtain ⟨_, e32, e64⟩ := observationLoadExpansion hm.active hb hend hcover
  cases afterSide with
  | false =>
      have r := uniswapV3Pool_block_13410 (immWords := wordsOf (immStore v)) hov
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [Bool.false_eq_true, ↓reduceIte] at ht hs e32 e64
      simpa only [uniswapV3Pool_block_13410_stack, u256_add_comm (UInt256.ofNat 32) beforePtr,
        u256_add_comm (UInt256.ofNat 64) beforePtr, ht, hs, e32, e64,
        memExpansionCost, Nat.sub_self, Nat.add_zero] using r
  | true =>
      have r := uniswapV3Pool_block_13450 (immWords := wordsOf (immStore v)) hov
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [↓reduceIte] at ht hs e32 e64
      simpa only [uniswapV3Pool_block_13450_stack, u256_add_comm (UInt256.ofNat 32) afterPtr,
        u256_add_comm (UInt256.ofNat 64) afterPtr, ht, hs, e32, e64,
        memExpansionCost, Nat.sub_self, Nat.add_zero] using r

end Benchmarks.UniswapV3.Pool
