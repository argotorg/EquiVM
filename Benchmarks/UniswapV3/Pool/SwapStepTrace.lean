import Benchmarks.UniswapV3.Pool.SwapStepPriceTrace
import Benchmarks.UniswapV3.Pool.SwapStepAmountsTrace
import Benchmarks.UniswapV3.Pool.SwapStepFeeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

noncomputable def swapStepRawResults (a : SwapStepArgs) (currentRaw targetRaw : UInt256) :
    List UInt256 :=
  [swapStepFee a, swapStepOutput a, swapStepAmount a true, swapStepRawPrice a currentRaw targetRaw]

theorem swapStepX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
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
    (swapStepValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (swapStepRawResults a currentRaw targetRaw ++ R) mem aw rdata σ k' C') := by
  rcases swapStepPriceX (v := v) a rd hc ht hl hf ha (by simpa only [List.length_cons] using hov)
      with ⟨hbad, rr⟩ | ⟨hp, kp, Cp, rp⟩
  · exact Or.inl ⟨fun h ↦ hbad h.1.1, rr⟩
  · rcases swapStepAmountsX (v := v) a rp hc ht hl ha hp (by simp only [List.length_cons]; omega)
        with ⟨hbad, rr⟩ | ⟨hm, km, Cm, rm⟩
    · exact Or.inl ⟨fun h ↦ hbad h.1, Or.inl rr⟩
    · obtain ⟨kc, Cc, rc⟩ := swapStepCapX (v := v) a rm
        (by simp only [List.length_cons]; omega)
      rcases swapStepFeeX (v := v) a rc hc ht hf ha hp
          (by simp only [List.length_cons]; omega) with ⟨hbad, rr⟩ | ⟨hf, kf, Cf, rf⟩
      · exact Or.inl ⟨fun h ↦ hbad h.2, Or.inl rr⟩
      · have rr := uniswapV3Pool_block_12930 (immWords := wordsOf (immStore v))
          (by evm_ov) hret rf
        refine Or.inr ⟨⟨hm, hf⟩, ?_⟩
        simpa only [uniswapV3Pool_block_12930_stack, swapStepRawResults,
          List.cons_append, List.nil_append] using RD.pack rr

end Benchmarks.UniswapV3.Pool
