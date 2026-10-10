import Benchmarks.UniswapV3.Pool.OracleSearchBefore
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_070
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_071

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSearchFoundX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw left right beforePtr afterPtr : UInt256}
    {cardRaw indexRaw targetRaw timeRaw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (first second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20742⟩
      ((if first && second then ⟨1⟩ else ⟨0⟩) :: (if first then ⟨1⟩ else ⟨0⟩) ::
        oracleSearchStack (oracleSearchMiddle left right) left right beforePtr afterPtr
          cardRaw indexRaw targetRaw timeRaw ret R) mem aw rdata σ k C)
    (hf : (first && second) = true)
    (hret : (D_J (deployedRuntime v) 0).contains ret = true) (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ret (afterPtr :: beforePtr :: R)
      mem aw rdata σ k' C' := by
  have r1 := uniswapV3Pool_block_20742_fallthrough (immWords := wordsOf (immStore v))
    (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
    (by rw [if_pos hf]; decide) rd
  have r2 := uniswapV3Pool_block_20748 (immWords := wordsOf (immStore v))
    (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
  have r3 := uniswapV3Pool_block_20782 (immWords := wordsOf (immStore v))
    (by evm_ov) hret r2
  refine ⟨k + 4 + 3 + 13, C + 17 + 13 + 34, by omega, ?_⟩
  exact r3

theorem oracleSearchAdvanceX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw left right beforePtr afterPtr : UInt256}
    {cardRaw indexRaw targetRaw timeRaw ret : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables} (first second : Bool)
    (rd : RD (deployedRuntime v) ee g s0 ⟨20742⟩
      ((if first && second then ⟨1⟩ else ⟨0⟩) :: (if first then ⟨1⟩ else ⟨0⟩) ::
        oracleSearchStack (oracleSearchMiddle left right) left right beforePtr afterPtr
          cardRaw indexRaw targetRaw timeRaw ret R) mem aw rdata σ k C)
    (hf : (first && second) = false) (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', C ≤ C' ∧ RD (deployedRuntime v) ee g s0 ⟨20441⟩
      (oracleSearchStack (oracleSearchMiddle left right)
        (if first then oracleSearchMiddle left right + ⟨1⟩ else left)
        (if first then right else UInt256.sub (oracleSearchMiddle left right) ⟨1⟩)
        beforePtr afterPtr cardRaw indexRaw targetRaw timeRaw ret R) mem aw rdata σ k' C' := by
  have r1 := uniswapV3Pool_block_20742_taken (immWords := wordsOf (immStore v))
    (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega)) (by rw [hf]; decide)
    (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
  cases first with
  | true =>
      have r2 := uniswapV3Pool_block_20753_taken (immWords := wordsOf (immStore v))
        (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega)) (by decide)
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r1
      have r3 := uniswapV3Pool_block_20769 (immWords := wordsOf (immStore v))
        (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega)) r2
      have r4 := uniswapV3Pool_block_20776 (immWords := wordsOf (immStore v))
        (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
      refine ⟨k + 4 + 4 + 6 + 4, C + 17 + 17 + 15 + 14, by omega, ?_⟩
      simpa only [uniswapV3Pool_block_20776_stack, uniswapV3Pool_block_20769_stack,
        uniswapV3Pool_block_20742_taken_stack, oracleSearchStack, ↓reduceIte,
        u256_add_comm (UInt256.ofNat 1)] using r4
  | false =>
      have r2 := uniswapV3Pool_block_20753_fallthrough (immWords := wordsOf (immStore v))
        (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega)) (by decide) r1
      have r3 := uniswapV3Pool_block_20759 (immWords := wordsOf (immStore v))
        (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r2
      have r4 := uniswapV3Pool_block_20776 (immWords := wordsOf (immStore v))
        (by first | omega | (dsimp only [oracleSearchStack, List.length]; omega))
        (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) r3
      refine ⟨k + 4 + 4 + 7 + 4, C + 17 + 17 + 25 + 14, by omega, ?_⟩
      exact r4

end Benchmarks.UniswapV3.Pool
