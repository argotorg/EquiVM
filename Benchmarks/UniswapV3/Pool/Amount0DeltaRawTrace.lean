import Benchmarks.UniswapV3.Pool.AmountDeltaRawWords
import Benchmarks.UniswapV3.Pool.FullMathRoundTrace
import Benchmarks.UniswapV3.Pool.UnsafeDivRoundTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_061

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def amount0DeltaRawComputeWords (a : AmountDeltaArgs)
    (liquidityRaw upperRaw lowerRaw : UInt256) : List UInt256 :=
  [amountDeltaDifference a, amountDeltaNumerator a, ⟨0⟩, a.roundUp.toUInt256,
    liquidityRaw, upperRaw, lowerRaw]

theorem amount0DeltaRawComputeX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : AmountDeltaArgs)
    (liquidityRaw upperRaw lowerRaw : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨18217⟩
      (amount0DeltaRawComputeWords a liquidityRaw upperRaw lowerRaw ++ ret :: R) mem aw rdata σ k C)
    (hU : UInt256.land upperRaw (UInt256.ofNat (2 ^ 160 - 1)) = amountDeltaUpper a)
    (hD : UInt256.land lowerRaw (UInt256.ofNat (2 ^ 160 - 1)) = amountDeltaLower a)
    (hfit : a.Fits) (hv : amountDeltaValid false a)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 30 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ret
      (amountDeltaResult false a :: R) mem aw rdata σ k' C' := by
  have ha : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) lowerRaw = amountDeltaLower a := by
    rw [amountDeltaMask160, u256_land_comm, hD]
  have hb : UInt256.land (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1)
      (UInt256.ofNat 160)) (UInt256.ofNat 1)) upperRaw = amountDeltaUpper a := by
    rw [amountDeltaMask160, u256_land_comm, hU]
  have hn : amountDeltaLower a ≠ UInt256.ofNat 0 := by
    intro hz
    have hp := hv.resolve_left (by decide)
    rw [hz] at hp
    exact Nat.not_lt_zero _ hp
  have hm : fullMathRoundValid (amountDeltaNumerator a) (amountDeltaDifference a)
      (amountDeltaUpper a) := amountDeltaMulValid false a hfit hv
  simp only [amount0DeltaRawComputeWords, List.cons_append, List.nil_append] at rd
  cases hr : a.roundUp
  · rw [hr] at rd
    have r1 := uniswapV3Pool_block_18217_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) rfl rd
    have r2 := uniswapV3Pool_block_18223 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_18223_stack, ha, hb] at r2
    rcases fullMathX (v := v) r2 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by evm_ov) with ⟨hbad, _⟩ | ⟨_, kr, Cr, _, rr⟩
    · exact False.elim (hbad hm.1)
    · have r3 := uniswapV3Pool_block_18252_taken (immWords := wordsOf (immStore v))
        (by evm_ov) hn (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
      have r4 := uniswapV3Pool_block_18259 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
      have r5 := uniswapV3Pool_block_18303 (immWords := wordsOf (immStore v)) (by evm_ov) hret r4
      simp only [amountDeltaResult, amountDeltaMulResult, amountDeltaFactor, amountDeltaDenominator,
        hr, Bool.false_eq_true, if_false]
      exact ⟨_, _, r5⟩
  · rw [hr] at rd
    have r1 := uniswapV3Pool_block_18217_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r2 := uniswapV3Pool_block_18265 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
    simp only [uniswapV3Pool_block_18265_stack, hb] at r2
    rcases fullMathRoundX (v := v) r2 (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest)
      (by evm_ov) with ⟨hbad, _⟩ | ⟨_, kr, Cr, _, rr⟩
    · exact False.elim (hbad hm)
    · have r3 := uniswapV3Pool_block_18288 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rr
      simp only [uniswapV3Pool_block_18288_stack, ha] at r3
      obtain ⟨_, _, r4⟩ := unsafeDivRoundX (v := v) r3
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
      have r5 := uniswapV3Pool_block_18303 (immWords := wordsOf (immStore v)) (by evm_ov) hret r4
      simp only [amountDeltaResult, amountDeltaMulResult, amountDeltaFactor, amountDeltaDenominator,
        hr, Bool.false_eq_true, if_false, if_true]
      exact ⟨_, _, r5⟩

theorem amount0DeltaRawX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (a : AmountDeltaArgs)
    (sqrtARaw sqrtBRaw liquidityRaw : UInt256)
    (rd : RD (deployedRuntime v) ee g s0 ⟨18125⟩
      (amountDeltaRawEntryWords a sqrtARaw sqrtBRaw liquidityRaw ++ ret :: R) mem aw rdata σ k C)
    (hfit : a.Fits)
    (hA : UInt256.land sqrtARaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtA)
    (hB : UInt256.land sqrtBRaw (UInt256.ofNat (2 ^ 160 - 1)) = a.sqrtB)
    (hL : UInt256.land liquidityRaw (UInt256.ofNat (2 ^ 128 - 1)) = a.liquidity)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true)
    (hov : R.length + 30 ≤ 1024) :
    (¬amountDeltaValid false a ∧ RDrev (deployedRuntime v) g s0) ∨
      (amountDeltaValid false a ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ret
        (amountDeltaResult false a :: R) mem aw rdata σ k' C') := by
  obtain ⟨_, _, r0⟩ := amountDeltaRawSortX (v := v) false a sqrtARaw sqrtBRaw liquidityRaw
    rd hA hB (by omega)
  have hs := amountDeltaRawSortedClean a sqrtARaw sqrtBRaw hA hB
  have hc : UInt256.land (amountDeltaRawLower a sqrtARaw sqrtBRaw)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = amountDeltaLower a := by
    rw [amountDeltaMask160, hs.1]
  simp only [amountDeltaRawSortedWords, List.cons_append, List.nil_append] at r0
  by_cases hv : amountDeltaValid false a
  · have hn : amountDeltaLower a ≠ UInt256.ofNat 0 := by
      intro hz
      have hp := hv.resolve_left (by decide)
      rw [hz] at hp
      exact Nat.not_lt_zero _ hp
    have r1 := uniswapV3Pool_block_18157_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by simpa only [hc] using hn)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    have hd := amountDeltaRawDifference a _ _ hs.2 hs.1
    simp only [uniswapV3Pool_block_18157_taken_stack, hd,
      amountDeltaRawNumerator a liquidityRaw hL] at r1
    exact Or.inr ⟨hv,
      amount0DeltaRawComputeX (v := v) a liquidityRaw _ _ r1 hs.2 hs.1 hfit hv hret hov⟩
  · have hz : amountDeltaLower a = UInt256.ofNat 0 := by
      apply uint256_toNat_eq_zero
      have hp : ¬0 < (amountDeltaLower a).toNat := fun h ↦ hv (Or.inr h)
      omega
    have r1 := uniswapV3Pool_block_18157_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (hc.trans hz) r0
    unfold uniswapV3Pool_block_18157_fallthrough_stack at r1
    exact Or.inl ⟨hv, uniswapV3Pool_block_18213 (immWords := wordsOf (immStore v)) (by evm_ov) r1⟩

end Benchmarks.UniswapV3.Pool
