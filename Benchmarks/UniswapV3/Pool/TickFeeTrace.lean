import Benchmarks.UniswapV3.Pool.TickFeePrefixTrace
import Benchmarks.UniswapV3.Pool.TickFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem tickFeeFinishX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickFeeArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21476⟩
      (tickFeeSide a σ ee false true :: tickFeeSide a σ ee false false ::
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.upper) ::
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.lower) :: ⟨0⟩ :: ⟨0⟩ ::
        a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (tickFeeInside a σ ee true :: tickFeeInside a σ ee false :: R) mem aw rdata σ k' C' := by
  rcases hfit with ⟨hlb, hub, hcb⟩
  have hu : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.upper) =
      EVM.wordOfInt a.upper := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hub.1 hub.2]
  have hc : UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.current) =
      EVM.wordOfInt a.current := by
    rw [signextend_wordOfInt ⟨24, by decide⟩ _ _ (by decide) (by decide),
      normalizeSint_eq_self ⟨24, by decide⟩ _ hcb.1 hcb.2]
  have hcmp : UInt256.slt (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.current))
      (UInt256.signextend (UInt256.ofNat 2) (EVM.wordOfInt a.upper)) =
      if a.current < a.upper then ⟨1⟩ else ⟨0⟩ := by
    rw [hc, hu]
    exact slt_wordOfInt _ _ (by omega) (by omega) (by omega) (by omega)
  have rready : ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨21529⟩
      (tickFeeSide a σ ee true true :: tickFeeSide a σ ee true false ::
        tickFeeSide a σ ee false true :: tickFeeSide a σ ee false false ::
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.upper) ::
        solcMappingSlot ⟨5⟩ (EVM.wordOfInt a.lower) :: ⟨0⟩ :: ⟨0⟩ ::
        a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R) mem aw rdata σ k' C' := by
    by_cases hd : a.current < a.upper
    · have rr := uniswapV3Pool_block_21476_fallthrough (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hcmp, if_pos hd]; rfl) rd
      obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21494 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rr
      refine ⟨kf, Cf, ?_⟩
      simpa only [uniswapV3Pool_block_21494_stack, tickFeeSide, TickFeeArgs.direct,
        TickFeeArgs.boundary, Bool.false_eq_true, if_false, if_true, if_pos hd,
        tickFeeOutside, tickFieldSlot] using rf
    · have rr := uniswapV3Pool_block_21476_taken (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [hcmp, if_neg hd]; decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; native_decide) rd
      obtain ⟨kf, Cf, rf⟩ := uniswapV3Pool_block_21510 (immWords := wordsOf (immStore v))
        (by evm_ov) rr
      refine ⟨kf, Cf, ?_⟩
      simpa only [uniswapV3Pool_block_21510_stack, tickFeeSide, TickFeeArgs.direct,
        TickFeeArgs.boundary, TickFeeArgs.global, Bool.false_eq_true, if_false, if_true,
        if_neg hd, tickFeeOutside, tickFieldSlot, u256_add_comm] using rf
  obtain ⟨kr, Cr, rr⟩ := rready
  have rf := uniswapV3Pool_block_21529 (immWords := wordsOf (immStore v))
    (by evm_ov) hret rr
  simp only [uniswapV3Pool_block_21529_stack] at rf
  exact ⟨_, _, rf⟩

theorem tickFeeExactX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickFeeArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21387⟩
      (a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (tickFeeInside a σ ee true :: tickFeeInside a σ ee false :: R)
      (tickFeeMemory mem a) (tickFeeMemoryWords aw) rdata σ k' C' := by
  obtain ⟨kp, Cp, rp⟩ := tickFeePrefixExactX (v := v) a rd hfit hov
  obtain ⟨kf, Cf, rf⟩ := tickFeeFinishX (v := v) a rp hfit hret hov
  exact ⟨kf, Cf, rf⟩


theorem tickFeeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : TickFeeArgs)
    (rd : RD (deployedRuntime v) ee g s0 ⟨21387⟩
      (a.global1 :: a.global0 :: EVM.wordOfInt a.current :: EVM.wordOfInt a.upper ::
        EVM.wordOfInt a.lower :: ⟨5⟩ :: ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits) (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C' aw', RD (deployedRuntime v) ee g s0 ret
      (tickFeeInside a σ ee true :: tickFeeInside a σ ee false :: R)
      (tickFeeMemory mem a) aw' rdata σ k' C' := by
  obtain ⟨k', C', r'⟩ := tickFeeExactX (v := v) a rd hfit hret hov
  exact ⟨k', C', _, r'⟩

end Benchmarks.UniswapV3.Pool
