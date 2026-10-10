import Benchmarks.UniswapV3.Pool.AmountDeltaRawWords
import Benchmarks.UniswapV3.Pool.FullMathRoundTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem amount1DeltaRawComputeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : AmountDeltaArgs)
    (liquidityRaw upperRaw lowerRaw : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨18034⟩
      (⟨0⟩ :: a.roundUp.toUInt256 :: liquidityRaw :: upperRaw :: lowerRaw :: ret :: R)
      mem aw rdata σ k C)
    (hfit : a.Fits)
    (hL : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hU : UInt256.land upperRaw (UInt256.ofNat (2 ^ 160 - 1)) = amountDeltaUpper a)
    (hD : UInt256.land lowerRaw (UInt256.ofNat (2 ^ 160 - 1)) = amountDeltaLower a)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 27 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (amountDeltaResult true a :: R) mem aw rdata σ k' C' := by
  have hq : UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 96) =
      UInt256.ofNat (2 ^ 96) := by native_decide
  have hmask : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 128))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 128 - 1) := solcMask128
  have hl : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 128)) (UInt256.ofNat 1)) liquidityRaw = a.liquidity := by
    rw [hmask, u256_land_comm, hL]
  have hd := amountDeltaRawDifference a upperRaw lowerRaw hU hD
  have hv : fullMathRoundValid a.liquidity (amountDeltaDifference a) (UInt256.ofNat (2 ^ 96)) :=
    amountDeltaMulValid true a hfit (Or.inl rfl)
  cases hr : a.roundUp
  · rw [hr] at rd
    have r1 := uniswapV3Pool_block_18034_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) rfl rd
    have r2 := uniswapV3Pool_block_18040 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_18040_stack, hq, hl, hd] at r2
    rcases fullMathX (v := v) r2 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by evm_ov) with ⟨hbad, _⟩ | ⟨_, kr, Cr, _, rr⟩
    · exact False.elim (hbad hv.1)
    · have r3 := uniswapV3Pool_block_18074 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
      have r4 := uniswapV3Pool_block_18114 (immWords := wordsOf (immStore v)) (by evm_ov) r3
      have r5 := uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v)) (by evm_ov) hret r4
      simp only [amountDeltaResult, amountDeltaMulResult, amountDeltaFactor, amountDeltaDenominator,
        hr, Bool.false_eq_true, if_false, if_true]
      exact ⟨_, _, r5⟩
  · rw [hr] at rd
    have r1 := uniswapV3Pool_block_18034_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_18079 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_18079_stack, hq, hl, hd] at r2
    rcases fullMathRoundX (v := v) r2 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by evm_ov) with ⟨hbad, _⟩ | ⟨_, kr, Cr, _, rr⟩
    · exact False.elim (hbad hv)
    · have r3 := uniswapV3Pool_block_18114 (immWords := wordsOf (immStore v)) (by evm_ov) rr
      have r4 := uniswapV3Pool_block_18117 (immWords := wordsOf (immStore v)) (by evm_ov) hret r3
      simp only [amountDeltaResult, amountDeltaMulResult, amountDeltaFactor, amountDeltaDenominator,
        hr, if_true]
      exact ⟨_, _, r4⟩

theorem amount1DeltaRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : AmountDeltaArgs)
    (sqrtARaw sqrtBRaw liquidityRaw : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨18002⟩
      (amountDeltaRawEntryWords a sqrtARaw sqrtBRaw liquidityRaw ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits)
    (hA : UInt256.land sqrtARaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtA)
    (hB : UInt256.land sqrtBRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtB)
    (hL : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 27 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (amountDeltaResult true a :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, rr⟩ := amountDeltaRawSortX (v := v) true a sqrtARaw sqrtBRaw liquidityRaw
    rd hA hB (by omega)
  have hs := amountDeltaRawSortedClean a sqrtARaw sqrtBRaw hA hB
  exact amount1DeltaRawComputeX (v := v) a liquidityRaw _ _ rr hfit hL hs.2 hs.1 hret hov

end Benchmarks.UniswapV3.Pool
