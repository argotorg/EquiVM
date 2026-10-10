import Benchmarks.UniswapV3.Pool.SwapStepMaxTrace
import Benchmarks.UniswapV3.Pool.SwapStepRecalcGuards
import Benchmarks.UniswapV3.Pool.SwapStepRecalcChoiceTrace
import Benchmarks.UniswapV3.Pool.SwapStepAmountsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapStepAmountsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw currentRaw targetRaw liquidityRaw feeRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables} (a : SwapStepArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨12654⟩
      (swapStepPriceWords a currentRaw targetRaw liquidityRaw feeRaw ++ R) mem aw rdata σ k C)
    (hc : UInt256.land currentRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.current)
    (ht : UInt256.land targetRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.target)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (ha : a.Fits) (hv : swapStepPriceValid a) (hov : R.length + 42 ≤ 1024) :
    (¬swapStepAmountsValid a ∧ RDrev (deployedRuntime v) g s0) ∨
    (swapStepAmountsValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨12827⟩
      (swapStepCalcWords a currentRaw targetRaw liquidityRaw feeRaw
        (swapStepAmount a true) (swapStepAmount a false) ++ R) mem aw rdata σ k' C') := by
  obtain ⟨km, Cm, rm⟩ := swapStepMaxX (v := v) a rd hc ht ha hv (by omega)
  obtain ⟨ki, Ci, ri⟩ := swapStepInputGuardX (v := v) (swapStepZeroForOne a)
    (swapStepMax a) (swapStepExactIn a) rm (by change R.length + 10 + 5 ≤ 1024; omega)
  have ri' : RD (deployedRuntime v) ee g s0 (swapStepRecalcGuardPC (swapStepZeroForOne a) true)
      ((swapStepKeep a true).toUInt256 ::
        swapStepRecalcWords a true currentRaw targetRaw liquidityRaw feeRaw
          (swapStepBeforeAmount a false) ++ R) mem aw rdata σ ki Ci := by
    simpa only [swapStepKeep, swapStepRecalcWords, swapStepCalcWords, if_true] using ri
  rcases swapStepRecalcChoiceX (v := v) a true ri' hc ht hl ha hv hov with
    ⟨hbad, rr⟩ | ⟨hi, ki', Ci', ri''⟩
  · exact Or.inl ⟨fun h ↦ hbad h.2.1, rr⟩
  · obtain ⟨ko, Co, ro⟩ := swapStepOutputGuardX (v := v) (swapStepZeroForOne a)
      (swapStepMax a) (swapStepExactIn a) ri'' (by change R.length + 6 + 9 ≤ 1024; omega)
    have ro' : RD (deployedRuntime v) ee g s0
        (swapStepRecalcGuardPC (swapStepZeroForOne a) false)
        ((swapStepKeep a false).toUInt256 ::
          swapStepRecalcWords a false currentRaw targetRaw liquidityRaw feeRaw
            (swapStepAmount a true) ++ R) mem aw rdata σ ko Co := by
      simpa only [swapStepKeep, swapStepRecalcWords, swapStepCalcWords,
        Bool.false_eq_true, if_false, if_true, List.cons_append, List.nil_append] using ro
    rcases swapStepRecalcChoiceX (v := v) a false ro' hc ht hl ha hv hov with
      ⟨hbad, rr⟩ | ⟨ho, ko', Co', ro''⟩
    · exact Or.inl ⟨fun h ↦ hbad h.2.2, rr⟩
    · refine Or.inr ⟨⟨hv, hi, ho⟩, ?_⟩
      cases hz : swapStepZeroForOne a
      · simp only [swapStepRecalcJoinPC, hz, Bool.false_eq_true, if_false] at ro''
        have rr := uniswapV3Pool_block_12824 (immWords := wordsOf (immStore v))
          (by change R.length + 7 + 6 ≤ 1024; omega) ro''
        simpa only [uniswapV3Pool_block_12824_stack, swapStepRecalcWords, swapStepCalcWords,
          Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using RD.pack rr
      · simp only [swapStepRecalcJoinPC, hz, Bool.false_eq_true, if_false, if_true] at ro''
        have rr := uniswapV3Pool_block_12746 (immWords := wordsOf (immStore v))
          (by change R.length + 7 + 6 ≤ 1024; omega)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) ro''
        simpa only [uniswapV3Pool_block_12746_stack, swapStepRecalcWords, swapStepCalcWords,
          Bool.false_eq_true, if_false, List.cons_append, List.nil_append] using RD.pack rr

end Benchmarks.UniswapV3.Pool
