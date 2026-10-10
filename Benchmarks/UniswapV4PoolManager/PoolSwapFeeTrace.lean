import Benchmarks.UniswapV4PoolManager.PoolSwapProtocolTrace
import Benchmarks.UniswapV4PoolManager.PoolSwapGrowthTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapFeeTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {s : PoolSwapStepWords}
    {aw step state liquidity tag x1 params remaining calculated fee protocol amount dir pool : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+17 ≤ 1024)
    (hfc : fee.toNat < 2^24) (hpc : protocol.toNat < 2^16) (hlc : liquidity.toNat < 2^128)
    (hi : memLoad (step+UInt256.ofNat 128) mem = s.amountIn)
    (hf : memLoad (step+UInt256.ofNat 192) mem = s.feeAmount)
    (hl : memLoad (state+UInt256.ofNat 64) (poolSwapProtocolMemory mem step s fee protocol) = liquidity)
    (hpf : memLoad (step+UInt256.ofNat 192) (poolSwapProtocolMemory mem step s fee protocol) =
      (poolSwapProtocolStep s fee protocol).feeAmount)
    (hpg : memLoad (step+UInt256.ofNat 224) (poolSwapProtocolMemory mem step s fee protocol) =
      (poolSwapProtocolStep s fee protocol).feeGrowthGlobal)
    (h : RD (deployedRuntime v) I g s0 ⟨19794⟩
      ([tag, x1, params, remaining, calculated, fee, protocol, amount, dir, step, pool, state]++R)
      mem aw rdata σ k C) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) I g s0 ⟨19833⟩
      ([⟨0⟩, tag, x1, params, remaining, calculated, fee, protocol,
        poolSwapProtocolAmount s fee protocol amount, dir, step, pool, state]++R)
      (poolSwapGrowthMemory (poolSwapProtocolMemory mem step s fee protocol) step
        (poolSwapProtocolStep s fee protocol) liquidity)
      (poolSwapGrowthAW (poolSwapProtocolAW aw step fee protocol) step state liquidity) rdata σ k' C' := by
  obtain ⟨k1, C1, hc1, rd1⟩ := poolSwapProtocolTrace v (by change R.length+2+15 ≤ 1024; omega) hfc hpc hi hf h
  obtain ⟨k2, C2, hc2, rd2⟩ := poolSwapGrowthTrace v (by change R.length+15 ≤ 1024; omega) hlc hl hpf hpg rd1
  exact ⟨k2, C2, hc1.trans hc2, rd2⟩

end Benchmarks.UniswapV4PoolManager
