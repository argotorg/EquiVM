import Benchmarks.UniswapV3.Pool.AmountDeltaRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem amountDeltaRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (second : Bool) (a : AmountDeltaArgs)
    (sqrtARaw sqrtBRaw liquidityRaw : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 (UInt256.ofNat (amountDeltaEntry second))
      (amountDeltaRawEntryWords a sqrtARaw sqrtBRaw liquidityRaw ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits)
    (hA : UInt256.land sqrtARaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtA)
    (hB : UInt256.land sqrtBRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtB)
    (hL : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    (¬amountDeltaValid second a ∧ RDrev (deployedRuntime v) g s0) ∨
      (amountDeltaValid second a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (amountDeltaResult second a :: R) mem aw rdata σ k' C') := by
  cases second
  · exact amount0DeltaRawX (v := v) a sqrtARaw sqrtBRaw liquidityRaw rd hfit hA hB hL hret hov
  · exact Or.inr ⟨Or.inl rfl,
      amount1DeltaRawX (v := v) a sqrtARaw sqrtBRaw liquidityRaw rd hfit hA hB hL hret (by omega)⟩

end Benchmarks.UniswapV3.Pool
