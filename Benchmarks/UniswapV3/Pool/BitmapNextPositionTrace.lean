import Benchmarks.UniswapV3.Pool.BitmapNextPrefixTrace
import Benchmarks.UniswapV3.Pool.BitmapPositionTrace
import Benchmarks.UniswapV3.Pool.BitmapPositionLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem bitmapNextPositionX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (compressed : Int) (lte : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨11376⟩
      (EVM.wordOfInt compressed :: ⟨0⟩ :: ⟨0⟩ :: (if lte then ⟨1⟩ else ⟨0⟩) :: R)
      mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 (if lte then ⟨11394⟩ else ⟨11508⟩)
      (bitmapPositionBitRaw (bitmapNextPosition compressed lte) ::
        EVM.wordOfInt (bitmapWordPos (bitmapNextPosition compressed lte)) ::
        ⟨0⟩ :: ⟨0⟩ :: EVM.wordOfInt compressed :: ⟨0⟩ :: ⟨0⟩ ::
        (if lte then ⟨1⟩ else ⟨0⟩) :: R) mem aw rdata σ k' C' := by
  cases lte
  · have r0 := uniswapV3Pool_block_11376_taken (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have r1 := uniswapV3Pool_block_11493 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    have ha : UInt256.ofNat 1 + EVM.wordOfInt compressed =
        EVM.wordOfInt (compressed + 1) := by
      rw [Int.add_comm compressed 1, wordOfInt_add]
      rfl
    simp only [uniswapV3Pool_block_11493_stack, ha] at r1
    have r2 := bitmapPositionX (v := v) (compressed + 1) r1
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    simpa only [bitmapNextPosition, Bool.false_eq_true, if_false,
      bitmapPositionBitRaw_normalize, bitmapWordPos_normalize] using r2
  · have r0 := uniswapV3Pool_block_11376_fallthrough (immWords := wordsOf (immStore v))
      (by evm_ov) (by decide) rd
    have r1 := uniswapV3Pool_block_11383 (immWords := wordsOf (immStore v))
      (by evm_ov) (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r0
    have r2 := bitmapPositionX (v := v) compressed r1
      (by rw [uniswapV3PoolPatchedValidJumps v]; jump_dest) (by evm_ov)
    exact r2

end Benchmarks.UniswapV3.Pool
