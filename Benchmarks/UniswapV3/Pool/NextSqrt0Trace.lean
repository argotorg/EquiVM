import Benchmarks.UniswapV3.Pool.NextSqrt0ChoiceTrace
import Benchmarks.UniswapV3.Pool.NextSqrt0FullTrace
import Benchmarks.UniswapV3.Pool.NextSqrt0FallbackTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool

theorem nextSqrt0X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨19939⟩
      ((if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount :: liquidityRaw :: priceRaw :: ret :: R)
      mem aw rdata σ k C)
    (hp : UInt256.land priceRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.price)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 31 ≤ 1024) :
    (¬nextSqrt0Valid a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (nextSqrt0Valid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (nextSqrt0RawResult a priceRaw :: R) mem aw rdata σ k' C') := by
  rcases nextSqrt0PrefixX (v := v) a rd hl hret (by omega) with ⟨hz, hr⟩ | ⟨hn, kp, Cp, rp⟩
  · refine Or.inr ⟨by simp only [nextSqrt0Valid, if_pos hz], ?_⟩
    simpa only [nextSqrt0RawResult, if_pos hz] using hr
  · obtain ⟨km, Cm, rm⟩ := nextSqrt0ProductX (v := v) a rp hp hn (by omega)
    cases ha : a.add
    · simp only [ha, Bool.false_eq_true, if_false] at rm
      rcases nextSqrt0SubtractGuardX (v := v) a rm (by evm_ov) with
        ⟨hb, hr⟩ | ⟨hs, ks, Cs, rs⟩
      · refine Or.inl ⟨?_, Or.inl hr⟩
        simp only [nextSqrt0Valid, if_neg hn, ha, Bool.false_eq_true, if_false]
        exact fun h ↦ hb h.1
      · rcases nextSqrt0SubtractFullX (v := v) a (by simpa only [ha] using rs)
          ha hp hret hov with ⟨hb, hr⟩ | ⟨hf, hc, hr⟩
        · refine Or.inl ⟨?_, Or.inl hr⟩
          simp only [nextSqrt0Valid, if_neg hn, ha, Bool.false_eq_true, if_false]
          exact fun h ↦ hb h.2
        · refine Or.inr ⟨?_, ?_⟩
          · simpa only [nextSqrt0Valid, if_neg hn, ha, Bool.false_eq_true, if_false]
              using And.intro hs (And.intro hf hc)
          · simpa only [nextSqrt0RawResult, if_neg hn, nextSqrt0Computed, ha,
              Bool.false_eq_true, false_and, if_false] using hr
    · simp only [ha, if_true] at rm
      rcases nextSqrt0AddChoiceX (v := v) a rm (by evm_ov) with
        ⟨hs, ks, Cs, rs⟩ | ⟨hs, ks, Cs, rs⟩
      · rcases nextSqrt0FallbackX (v := v) a (by simpa only [ha] using rs) hp hret
          (by omega) with ⟨hb, hr⟩ | ⟨hf, hr⟩
        · refine Or.inl ⟨?_, hr⟩
          simpa only [nextSqrt0Valid, if_neg hn, ha, if_true, if_neg hs] using hb
        · refine Or.inr ⟨?_, ?_⟩
          · simpa only [nextSqrt0Valid, if_neg hn, ha, if_true, if_neg hs] using hf
          · simpa only [nextSqrt0RawResult, if_neg hn, nextSqrt0Computed, ha,
              true_and, hs, not_false_eq_true, if_true] using hr
      · rcases nextSqrt0FastFullX (v := v) a (by simpa only [ha] using rs) ha hp hret
          (by omega) with ⟨hb, hr⟩ | ⟨hf, hr⟩
        · refine Or.inl ⟨?_, Or.inl hr⟩
          simpa only [nextSqrt0Valid, if_neg hn, ha, if_true, if_pos hs] using hb
        · refine Or.inr ⟨?_, ?_⟩
          · simpa only [nextSqrt0Valid, if_neg hn, ha, if_true, if_pos hs] using hf
          · simpa only [nextSqrt0RawResult, if_neg hn, nextSqrt0Computed, ha,
              true_and, hs, not_true_eq_false, if_false] using hr

end Benchmarks.UniswapV3.Pool
