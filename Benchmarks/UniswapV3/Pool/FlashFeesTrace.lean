import Benchmarks.UniswapV3.Pool.FlashFeesSource
import Benchmarks.UniswapV3.Pool.FullMathRoundTrace
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_023

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem flashFeesX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw liquidity len start amount0 amount1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨6595⟩
      (liquidity :: len :: start :: amount1 :: amount0 :: R) mem aw rdata σ k C)
    (hov : R.length + 28 ≤ 1024) :
    (RDrev (deployedRuntime v) g s0 ∧
      ¬ (fullMathRoundValid amount0 (poolFeeWord v) ⟨1000000⟩ ∧
        fullMathRoundValid amount1 (poolFeeWord v) ⟨1000000⟩)) ∨
    (fullMathRoundValid amount0 (poolFeeWord v) ⟨1000000⟩ ∧
      fullMathRoundValid amount1 (poolFeeWord v) ⟨1000000⟩ ∧
      ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨15572⟩
        (⟨6715⟩ :: ⟨0⟩ :: fullMathRoundResult amount1 (poolFeeWord v) ⟨1000000⟩ ::
          fullMathRoundResult amount0 (poolFeeWord v) ⟨1000000⟩ :: liquidity :: len :: start ::
          amount1 :: amount0 :: R) mem aw rdata σ k' C') := by
  have hfee : UInt256.land (UInt256.ofNat 16777215) (wordsOf (immStore v) "fee") =
      poolFeeWord v := by
    rw [wordsOf_immStore_fee, wordOfInt_ofNat_toNat_gen, u256_ofNat_toNat, u256_land_comm]
    rfl
  have rdFee0 := uniswapV3Pool_block_6595 (immWords := wordsOf (immStore v)) (by evm_ov)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  simp only [uniswapV3Pool_block_6595_stack, hfee] at rdFee0
  rcases fullMathRoundX (v := v) rdFee0
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
    ⟨hbad0, rdBad⟩ | ⟨hv0, k0, C0, _, rd0⟩
  · exact Or.inl ⟨rdBad, fun h ↦ hbad0 h.1⟩
  · have rdFee1 := uniswapV3Pool_block_6648 (immWords := wordsOf (immStore v)) (by evm_ov)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd0
    simp only [uniswapV3Pool_block_6648_stack, hfee] at rdFee1
    rcases fullMathRoundX (v := v) rdFee1
        (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov) with
      ⟨hbad1, rdBad⟩ | ⟨hv1, k1, C1, _, rd1⟩
    · exact Or.inl ⟨rdBad, fun h ↦ hbad1 h.2⟩
    · have rdBalance := uniswapV3Pool_block_6703 (immWords := wordsOf (immStore v)) (by evm_ov)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd1
      exact Or.inr ⟨hv0, hv1, _, _, rdBalance⟩

end Benchmarks.UniswapV3.Pool
