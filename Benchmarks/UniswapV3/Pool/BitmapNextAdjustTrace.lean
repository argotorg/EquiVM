import Benchmarks.UniswapV3.Pool.BitmapNextCompressedWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_035

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapNextAdjustX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (tick spacing : Int)
    (htlo : -(2 ^ 23 : Int) ≤ tick) (hthi : tick < 2 ^ 23) (hn : spacing ≠ 0)
    (rd : RD (deployedRuntime v) ee g s0 ⟨11366⟩
      ((if bitmapNextAdjust tick spacing then ⟨1⟩ else ⟨0⟩) ::
        EVM.wordOfInt (tick.tdiv spacing) :: R)
        mem aw rdata σ k C) (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨11376⟩
      (EVM.wordOfInt (bitmapNextCompressed tick spacing) :: R) mem aw rdata σ k' C' := by
  by_cases h : bitmapNextAdjust tick spacing
  · rw [if_pos h] at rd
    have r1 := uniswapV3Pool_block_11366_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) rd
    have r2 := uniswapV3Pool_block_11372 (immWords := wordsOf (immStore v)) (by evm_ov) r1
    simpa only [bitmapNextCompressed_word tick spacing htlo hthi hn, if_pos h,
      uniswapV3Pool_block_11372_stack] using RD.pack r2
  · rw [if_neg h] at rd
    have r1 := uniswapV3Pool_block_11366_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    simpa only [bitmapNextCompressed_word tick spacing htlo hthi hn, if_neg h] using RD.pack r1

end Benchmarks.UniswapV3.Pool
