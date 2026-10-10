import Benchmarks.UniswapV3.Pool.TickLogRunWords
import Benchmarks.UniswapV3.Pool.RuntimeBlocks_047

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogSquaresStack1 (square : Nat → UInt256) (msb : UInt256) (R : List UInt256) : List UInt256 :=
  square 6 :: square 6 :: square 5 :: square 4 :: square 3 :: square 2 :: square 1 ::
    ⟨255⟩ :: ⟨127⟩ :: square 0 :: msb :: R

theorem tickLogSquaresBlock1_eq (r msb : UInt256) (R : List UInt256) :
    uniswapV3Pool_block_14273_stack (x0 := msb) (x1 := r) (R := R) =
      tickLogSquaresStack1 (tickLogCompiledSquareAt r) msb R := by
  rfl

theorem tickLogSquares1X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw r msb : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14273⟩ (msb :: r :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14339⟩
      (tickLogSquaresStack1 (tickLogSquareAt r) msb R) mem aw rdata σ k' C' := by
  have hs : tickLogCompiledSquareAt r = tickLogSquareAt r :=
    funext (tickLogCompiledSquareAt_eq r)
  have rout := uniswapV3Pool_block_14273 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  exact ⟨_, _, by simpa only [tickLogSquaresBlock1_eq, hs] using rout⟩

def tickLogSquaresStack2 (run square : Nat → UInt256)
    (old5 old4 old3 old2 old1 : UInt256) (R : List UInt256) : List UInt256 :=
  run 7 :: square 5 :: square 4 :: square 3 :: square 2 :: square 1 :: square 0 ::
    old5 :: old4 :: old3 :: old2 :: old1 :: square 6 :: ⟨127⟩ :: R

theorem tickLogSquaresBlock2_eq (r old5 old4 old3 old2 old1 : UInt256) (R : List UInt256) :
    uniswapV3Pool_block_14339_stack (x0 := tickLogSquare r) (x1 := tickLogSquare r)
      (x2 := old5) (x3 := old4) (x4 := old3) (x5 := old2) (x6 := old1)
      (x7 := ⟨255⟩) (x8 := ⟨127⟩) (R := R) =
      tickLogSquaresStack2 (tickLogCompiledRun r) (tickLogCompiledSquareAt r)
        old5 old4 old3 old2 old1 R := by
  rfl

theorem tickLogSquares2X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw r old5 old4 old3 old2 old1 : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14339⟩
      (tickLogSquare r :: tickLogSquare r :: old5 :: old4 :: old3 :: old2 :: old1 ::
        ⟨255⟩ :: ⟨127⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 16 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14403⟩
      (tickLogSquaresStack2 (tickLogRun r) (tickLogSquareAt r)
        old5 old4 old3 old2 old1 R) mem aw rdata σ k' C' := by
  have hr : tickLogCompiledRun r = tickLogRun r := funext (tickLogCompiledRun_eq r)
  have hs : tickLogCompiledSquareAt r = tickLogSquareAt r :=
    funext (tickLogCompiledSquareAt_eq r)
  have rout := uniswapV3Pool_block_14339 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  exact ⟨_, _, by simpa only [tickLogSquaresBlock2_eq, hr, hs] using rout⟩

def tickLogSquaresStack (r msb : UInt256) (R : List UInt256) : List UInt256 :=
  tickLogRun r 13 :: tickLogSquareAt r 11 :: tickLogSquareAt r 10 :: tickLogSquareAt r 9 ::
    tickLogSquareAt r 8 :: tickLogSquareAt r 7 :: tickLogSquareAt r 6 ::
    tickLogSquareAt r 5 :: tickLogSquareAt r 4 :: tickLogSquareAt r 3 :: tickLogSquareAt r 2 ::
    tickLogSquareAt r 1 :: tickLogSquareAt r 12 :: ⟨127⟩ :: tickLogSquareAt r 0 :: msb :: R

theorem tickLogSquaresX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw r msb : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14273⟩ (msb :: r :: R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14403⟩
      (tickLogSquaresStack r msb R) mem aw rdata σ k' C' := by
  obtain ⟨k', C', r1⟩ := tickLogSquares1X rd (by omega)
  unfold tickLogSquaresStack1 at r1
  have rout := tickLogSquares2X (r := tickLogRun r 6) r1 (by evm_ov)
  simpa only [tickLogSquaresStack, tickLogSquaresStack2, tickLogRun_add,
    tickLogSquareAt_add, Nat.reduceAdd] using rout

end Benchmarks.UniswapV3.Pool
