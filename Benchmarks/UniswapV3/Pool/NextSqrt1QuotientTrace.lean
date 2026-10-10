import Benchmarks.UniswapV3.Pool.NextSqrt1PrefixTrace
import Benchmarks.UniswapV3.Pool.FullMathRoundTrace
import Benchmarks.UniswapV3.Pool.UnsafeDivRoundTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt1QuotientX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret priceRaw liquidityRaw : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (a : NextSqrtArgs)
    (rd : RD (deployedRuntime v) ee g s0 (nextSqrt1QuotientPC a)
      (⟨0⟩ :: ⟨0⟩ :: (if a.add then ⟨1⟩ else ⟨0⟩) :: a.amount ::
        liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k C)
    (hl : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hov : R.length + 28 ≤ 1024) :
    (¬nextSqrt1QuotientValid a ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (nextSqrt1QuotientValid a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0
      (if a.add then ⟨19792⟩ else ⟨19898⟩)
      (nextSqrt1Quotient a :: ⟨0⟩ :: ⟨0⟩ :: (if a.add then ⟨1⟩ else ⟨0⟩) ::
        a.amount :: liquidityRaw :: priceRaw :: ret :: R) mem aw rdata σ k' C') := by
  have hl' : UInt256.land (UInt256.ofNat (2 ^ 128 - 1)) liquidityRaw = a.liquidity := by
    rw [u256_land_comm]; exact hl
  have hq : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96) =
      UInt256.ofNat (2 ^ 96) := by decide
  cases ha : a.add
  · by_cases hsmall : nextSqrt1Small a
    · simp only [nextSqrt1QuotientPC, ha, Bool.false_eq_true, if_false, if_pos hsmall] at rd
      have r0 := uniswapV3Pool_block_19875 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [uniswapV3Pool_block_19875_stack, solcMask128, hl] at r0
      obtain ⟨kr, Cr, rr⟩ := unsafeDivRoundX (v := v) r0
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
      refine Or.inr ⟨by simp only [nextSqrt1QuotientValid, if_pos hsmall, ha,
        Bool.false_eq_true, false_implies], ?_⟩
      simpa only [nextSqrt1Quotient, if_pos hsmall, ha, Bool.false_eq_true,
        if_false, nextSqrt1ScaledAmount] using RD.pack rr
    · simp only [nextSqrt1QuotientPC, ha, Bool.false_eq_true, if_false, if_neg hsmall] at rd
      have r0 := uniswapV3Pool_block_19847 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [uniswapV3Pool_block_19847_stack, solcMask128, hl', hq] at r0
      rcases fullMathRoundX (v := v) r0
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
        ⟨hbad, hr⟩ | ⟨hv, kr, Cr, _, rr⟩
      · refine Or.inl ⟨?_, Or.inl hr⟩
        simpa only [nextSqrt1QuotientValid, if_neg hsmall, ha, Bool.false_eq_true, if_false]
          using hbad
      · have r1 := uniswapV3Pool_block_19870 (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
        refine Or.inr ⟨by simpa only [nextSqrt1QuotientValid, if_neg hsmall, ha,
          Bool.false_eq_true, if_false] using hv, ?_⟩
        simpa only [nextSqrt1Quotient, if_neg hsmall, ha, Bool.false_eq_true, if_false]
          using RD.pack r1
  · by_cases hsmall : nextSqrt1Small a
    · simp only [nextSqrt1QuotientPC, ha, if_true, if_pos hsmall] at rd
      by_cases hy : a.liquidity.toNat = 0
      · have hz : a.liquidity = (⟨0⟩ : UInt256) := uint256_toNat_eq_zero hy
        have r0 := uniswapV3Pool_block_19768_fallthrough (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hl, hz]; rfl) rd
        refine Or.inl ⟨?_, Or.inr (uniswapV3Pool_block_19789
          (immWords := wordsOf (immStore v)) r0)⟩
        simp only [nextSqrt1QuotientValid, if_pos hsmall, ha, true_implies, hy, ne_eq,
          not_true_eq_false,
          not_false_eq_true]
      · have hn : a.liquidity ≠ (UInt256.ofNat 0) := by
          intro he; exact hy (congrArg UInt256.toNat he)
        have r0 := uniswapV3Pool_block_19768_taken (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [solcMask128, hl]; exact hn)
          (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
        have r1 := uniswapV3Pool_block_19790 (immWords := wordsOf (immStore v)) (by evm_ov) r0
        refine Or.inr ⟨by simpa only [nextSqrt1QuotientValid, if_pos hsmall, ha, true_implies]
          using hy, ?_⟩
        simpa only [uniswapV3Pool_block_19790_stack, solcMask128, hl,
          nextSqrt1Quotient, if_pos hsmall, ha, if_true, nextSqrt1ScaledAmount] using RD.pack r1
    · simp only [nextSqrt1QuotientPC, ha, if_true, if_neg hsmall] at rd
      have r0 := uniswapV3Pool_block_19740 (immWords := wordsOf (immStore v))
        (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
      simp only [uniswapV3Pool_block_19740_stack, solcMask128, hl', hq] at r0
      rcases fullMathX (v := v) r0
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
        ⟨hbad, hr⟩ | ⟨hv, kr, Cr, _, rr⟩
      · refine Or.inl ⟨?_, Or.inl hr⟩
        simpa only [nextSqrt1QuotientValid, if_neg hsmall, ha, if_true] using hbad
      · have r1 := uniswapV3Pool_block_19763 (immWords := wordsOf (immStore v))
          (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
        refine Or.inr ⟨by simpa only [nextSqrt1QuotientValid, if_neg hsmall, ha, if_true]
          using hv, ?_⟩
        simpa only [nextSqrt1Quotient, if_neg hsmall, ha, if_true] using RD.pack r1

end Benchmarks.UniswapV3.Pool
