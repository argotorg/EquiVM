import Benchmarks.UniswapV3.Pool.NextSqrt1QuotientTrace
import Benchmarks.UniswapV3.Pool.NextSqrt1OutputTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem nextSqrt1X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19714⟩
      ((if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 28 ≤ 1024) :
    (¬nextSqrt1Valid a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (nextSqrt1Valid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (nextSqrt1Result a :: R) mem aw rdata σ k' C') := by
  obtain ⟨kp, Cp, rp⟩ := nextSqrt1PrefixX (v := v) a rd (by omega)
  rcases nextSqrt1QuotientX (v := v) a rp hl hov with ⟨hb, hr⟩ | ⟨hq, kq, Cq, rq⟩
  · exact Or.inl ⟨fun h ↦ hb h.1, hr⟩
  · rcases nextSqrt1OutputX (v := v) a rq hp hret (by omega) with ⟨hb, hr⟩ | ⟨ho, hr⟩
    · exact Or.inl ⟨fun h ↦ hb h.2, Or.inl hr⟩
    · exact Or.inr ⟨⟨hq, ho⟩, hr⟩

end Benchmarks.UniswapV3.Pool
