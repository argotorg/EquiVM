import Benchmarks.UniswapV3.Pool.SwapStepBudgetTrace
import Benchmarks.UniswapV3.Pool.SwapStepInitialTrace
import Benchmarks.UniswapV3.Pool.SwapStepInputPriceTrace
import Benchmarks.UniswapV3.Pool.SwapStepOutputPriceTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepPriceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12447⟩
      (swapStepRawWords a currentRaw targetRaw liquidityRaw feeRaw ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hf : UInt256.land feeRaw (UInt256.ofNat (2 ^ 24 - 1)) = a.fee)
    (ha : a.Fits) (hov : R.length + 49 ≤ 1024) :
    (¬swapStepPriceValid a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (swapStepPriceValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12654⟩
      (swapStepPriceWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
      mem aw rdata σ k' C') := by
  obtain ⟨kp, Cp, rp⟩ := swapStepPrefixX (v := v) a rd hc ht ha.2.2.2.1 (by omega)
  cases hi : swapStepExactIn a
  · simp only [swapStepBranchPC, hi, Bool.false_eq_true, if_false] at rp
    rcases swapStepOutputDeltaX (v := v) a rp hc ht hl ha (by omega) with
      ⟨hbad, rr⟩ | ⟨hd, kd, Cd, rd⟩
    · refine Or.inl ⟨?_, Or.inl rr⟩
      intro hv
      exact hbad (by simpa only [swapStepInitialValid, hi] using hv.2.1)
    · have ri : RD (deployedRuntime v) ee g s0 ⟨12616⟩
          (swapStepInitialDelta a ::
            swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
          mem aw rdata σ kd Cd := by
        simpa only [swapStepInitialDelta, swapStepInitialAmount, hi] using rd
      rcases swapStepOutputPriceX (v := v) a ri hc hl hi (by omega) with
        ⟨hbad, rr⟩ | ⟨hv, kr, Cr, rr⟩
      · exact Or.inl ⟨fun h ↦ hbad h.2.2, rr⟩
      · refine Or.inr ⟨⟨?_, ?_, hv⟩, kr, Cr, rr⟩
        · simp only [swapStepBudgetValid, hi, Bool.false_eq_true, if_false]
        · simpa only [swapStepInitialValid, hi] using hd
  · simp only [swapStepBranchPC, hi, if_true] at rp
    rcases swapStepBudgetX (v := v) a rp hf hi (by omega) with
      ⟨hbad, rr⟩ | ⟨hb, kb, Cb, rb⟩
    · exact Or.inl ⟨fun h ↦ hbad h.1, Or.inl rr⟩
    · rcases swapStepInputDeltaX (v := v) a rb hc ht hl ha (by omega) with
        ⟨hbad, rr⟩ | ⟨hd, kd, Cd, rd⟩
      · refine Or.inl ⟨?_, Or.inl rr⟩
        intro hv
        exact hbad (by simpa only [swapStepInitialValid, hi] using hv.2.1)
      · have ri : RD (deployedRuntime v) ee g s0 ⟨12542⟩
            (swapStepInitialDelta a :: swapStepBudget a ::
              swapStepReadyWords a currentRaw targetRaw liquidityRaw feeRaw ++ R)
            mem aw rdata σ kd Cd := by
          simpa only [swapStepInitialDelta, swapStepInitialAmount, hi] using rd
        rcases swapStepInputPriceX (v := v) a ri hc hl hi hov with
          ⟨hbad, rr⟩ | ⟨hv, kr, Cr, rr⟩
        · exact Or.inl ⟨fun h ↦ hbad h.2.2, rr⟩
        · refine Or.inr ⟨⟨hb, ?_, hv⟩, kr, Cr, rr⟩
          simpa only [swapStepInitialValid, hi] using hd

end Benchmarks.UniswapV3.Pool
