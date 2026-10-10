import Benchmarks.UniswapV3.Pool.OracleObserveReturnTrace
import Benchmarks.UniswapV3.Pool.ObservationCoverage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleObserveZeroLoadX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw free ptr z0 z1 : UInt256} {obs : OracleObservation}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨13340⟩ (ptr :: z0 :: z1 :: R) mem aw rdata σ k C)
    (hm : HeapMemory mem aw free) (hb : free.toNat ≤ 2 ^ 200)
    (hobs : ObservationMemory mem ptr obs) (hend : ptr.toNat + 128 ≤ free.toNat)
    (hcover : free.toNat ≤ aw.toNat * 32 + 32) (hov : R.length + 6 ≤ 1024) :
    RD (deployedRuntime v) ee g s0 ⟨13584⟩
      (obs.secondsPerLiquidity :: EVM.wordOfInt obs.tickCumulative :: R)
      mem aw rdata σ (k + 16) (C + 48) := by
  have hbound : ptr.toNat + 128 < UInt256.size := by change _ < 2 ^ 256; omega
  have ht := hobs.load_tick hbound
  have hs := hobs.load_seconds hbound
  obtain ⟨_, e32, e64⟩ := observationLoadExpansion hm.active hb hend hcover
  have r := uniswapV3Pool_block_13340 (immWords := wordsOf (immStore v)) hov
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simpa only [uniswapV3Pool_block_13340_stack, u256_add_comm (UInt256.ofNat 32) ptr,
    u256_add_comm (UInt256.ofNat 64) ptr, ht, hs, e32, e64,
    memExpansionCost, Nat.sub_self, Nat.add_zero] using r

end Benchmarks.UniswapV3.Pool
