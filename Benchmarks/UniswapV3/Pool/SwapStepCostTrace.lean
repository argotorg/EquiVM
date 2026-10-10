import Benchmarks.UniswapV3.Pool.SwapStepTrace
import Benchmarks.UniswapV3.Pool.ReachRoutineCost

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem swapStepMonoX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12447⟩
      (swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw ++ ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hf : UInt256.land feeRaw (UInt256.ofNat (2 ^ 24 - 1)) = a.fee)
    (ha : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 50 ≤ 1024) :
    (¬swapStepValid a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (swapStepValid a ∧ ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret
      (swapStepRawResults a currentRaw targetRaw ++ R) mem aw rdata σ k' C') := by
  apply rdRoutine_mono rd
  intro gas start rr
  exact swapStepX (v := v) a rr hc ht hl hf ha hret hov

end Benchmarks.UniswapV3.Pool
