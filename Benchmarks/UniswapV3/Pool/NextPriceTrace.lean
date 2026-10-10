import Benchmarks.UniswapV3.Pool.NextPriceDirectionTrace
import Benchmarks.UniswapV3.Pool.NextSqrt0Trace
import Benchmarks.UniswapV3.Pool.NextSqrt1Trace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextPriceCalleeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (input : Bool) (a : NextPriceArgs)
    (rd : RD (deployedRuntime v) ee g s0 (nextPriceCalleePC input a)
      ((if input then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw ::
        nextPriceReturnPC a :: ⟨0⟩ :: (if a.zeroForOne then ⟨1⟩ else ⟨0⟩) ::
        a.amount :: liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 37 ≤ 1024) :
    (¬nextPriceCalleeValid input a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (nextPriceCalleeValid input a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (nextPriceRawResult input a priceRaw :: R) mem aw rdata σ k' C') := by
  have hc : (D_J (deployedRuntime v) 0).contains (nextPriceReturnPC a) = true := by
    cases hz : a.zeroForOne <;>
      simp only [nextPriceReturnPC, hz, Bool.false_eq_true, if_false, if_true] <;>
      rw [uniswapV3PoolPatchedValidJumps v] <;> jump_dest
  cases ho : nextPriceOne input a
  · simp only [nextPriceCalleePC, ho, Bool.false_eq_true, if_false] at rd
    rcases nextSqrt0X (v := v) (a.sqrtArgs input) rd hp hl hc (by evm_ov) with
      ⟨hb, hr⟩ | ⟨hv, kr, Cr, rr⟩
    · refine Or.inl ⟨?_, hr⟩
      simpa only [nextPriceCalleeValid, ho, Bool.false_eq_true, if_false] using hb
    · refine Or.inr ⟨?_, ?_⟩
      · simpa only [nextPriceCalleeValid, ho, Bool.false_eq_true, if_false] using hv
      · simpa only [nextPriceRawResult, ho, Bool.false_eq_true, if_false]
          using nextPriceReturnX (v := v) a rr hret (by omega)
  · simp only [nextPriceCalleePC, ho, if_true] at rd
    rcases nextSqrt1X (v := v) (a.sqrtArgs input) rd hp hl hc (by evm_ov) with
      ⟨hb, hr⟩ | ⟨hv, kr, Cr, rr⟩
    · refine Or.inl ⟨?_, hr⟩
      simpa only [nextPriceCalleeValid, ho, if_true] using hb
    · refine Or.inr ⟨?_, ?_⟩
      · simpa only [nextPriceCalleeValid, ho, if_true] using hv
      · simpa only [nextPriceRawResult, ho, if_true]
          using nextPriceReturnX (v := v) a rr hret (by omega)

theorem nextPriceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (input : Bool) (a : NextPriceArgs)
    (rd : RD (deployedRuntime v) ee g s0 (nextPriceEntry input)
      ((if a.zeroForOne then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw ::
        priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 37 ≤ 1024) :
    (¬nextPriceValid input a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (nextPriceValid input a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (nextPriceRawResult input a priceRaw :: R) mem aw rdata σ k' C') := by
  rcases nextPriceGuardX (v := v) input a rd hp hl (by omega) with
    ⟨hb, hr⟩ | ⟨hg, kg, Cg, rg⟩
  · exact Or.inl ⟨fun h ↦ hb h.1, Or.inl hr⟩
  · obtain ⟨kd, Cd, rd⟩ := nextPriceDirectionX (v := v) input a rg (by omega)
    rcases nextPriceCalleeX (v := v) input a rd hp hl hret hov with ⟨hb, hr⟩ | ⟨hv, hr⟩
    · exact Or.inl ⟨fun h ↦ hb h.2, hr⟩
    · exact Or.inr ⟨⟨hg, hv⟩, hr⟩

end Benchmarks.UniswapV3.Pool
