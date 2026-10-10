import Benchmarks.UniswapV3.Pool.TickLogSeriesWords
import Benchmarks.UniswapV3.Pool.TickLogSquaresTrace
import Benchmarks.UniswapV3.Pool.WordComplements

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem tickLogInitial_compiled (msb : Nat) :
    UInt256.shiftLeft (UInt256.ofNat msb + UInt256.lnot (UInt256.ofNat 127))
      (UInt256.ofNat 64) = tickLogInitial msb := by
  rw [wordAdd_lnot_eq_sub_addOne,
    show UInt256.ofNat 127 + (⟨1⟩ : UInt256) = ⟨128⟩ by decide]
  rfl

def tickLogAccStack1 (r : UInt256) (msb : Nat) (R : List UInt256) : List UInt256 :=
  tickLogSquareAt r 8 :: tickLogAccRun r (tickLogInitial msb) 4 :: tickLogSquareAt r 7 ::
    tickLogSquareAt r 6 :: tickLogSquareAt r 5 ::
    UInt256.land (UInt256.ofNat 576460752303423488)
      (UInt256.shiftRight (tickLogSquareAt r 4) (UInt256.ofNat 196)) ::
    tickLogSquareAt r 9 :: tickLogSquareAt r 10 :: tickLogSquareAt r 11 ::
    tickLogSquareAt r 12 :: tickLogSquareAt r 13 :: UInt256.ofNat msb ::
    tickLogScaled (tickLogRun r 13) :: R

theorem tickLogAcc1X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C msb : Nat} {aw r : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14403⟩
      (tickLogSquaresStack r (UInt256.ofNat msb) R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14514⟩
      (tickLogAccStack1 r msb R) mem aw rdata σ k' C' := by
  have h0 : UInt256.lor (UInt256.land (UInt256.ofNat 9223372036854775808)
      (UInt256.shiftRight (tickLogSquareAt r 0) (UInt256.ofNat 192)))
      (tickLogInitial msb) = tickLogAccRun r (tickLogInitial msb) 1 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 0 (by decide)
  have h1 : UInt256.lor (UInt256.land (UInt256.ofNat 4611686018427387904)
      (UInt256.shiftRight (tickLogSquareAt r 1) (UInt256.ofNat 193)))
      (tickLogAccRun r (tickLogInitial msb) 1) = tickLogAccRun r (tickLogInitial msb) 2 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 1 (by decide)
  have h2 : UInt256.lor (UInt256.land (UInt256.ofNat 2305843009213693952)
      (UInt256.shiftRight (tickLogSquareAt r 2) (UInt256.ofNat 194)))
      (tickLogAccRun r (tickLogInitial msb) 2) = tickLogAccRun r (tickLogInitial msb) 3 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 2 (by decide)
  have h3 : UInt256.lor (UInt256.land (UInt256.ofNat 1152921504606846976)
      (UInt256.shiftRight (tickLogSquareAt r 3) (UInt256.ofNat 195)))
      (tickLogAccRun r (tickLogInitial msb) 3) = tickLogAccRun r (tickLogInitial msb) 4 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 3 (by decide)
  unfold tickLogSquaresStack at rd
  have rout := uniswapV3Pool_block_14403 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  refine ⟨k + 64, C + 194, ?_⟩
  simpa only [uniswapV3Pool_block_14403_stack, tickLogAccStack1, tickLogInitial_compiled,
    h0, h1, h2, h3] using rout

def tickLogAccStack (r : UInt256) (msb : Nat) (R : List UInt256) : List UInt256 :=
  tickLogAccRun r (tickLogInitial msb) 12 :: tickLogSquareAt r 12 :: ⟨204⟩ ::
    tickLogSquareAt r 13 :: UInt256.ofNat msb :: tickLogScaled (tickLogRun r 13) :: R

theorem tickLogAcc2X {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C msb : Nat} {aw r : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14514⟩
      (tickLogAccStack1 r msb R) mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14638⟩
      (tickLogAccStack r msb R) mem aw rdata σ k' C' := by
  have h4 : UInt256.lor (UInt256.land (UInt256.ofNat 576460752303423488)
      (UInt256.shiftRight (tickLogSquareAt r 4) (UInt256.ofNat 196)))
      (tickLogAccRun r (tickLogInitial msb) 4) = tickLogAccRun r (tickLogInitial msb) 5 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 4 (by decide)
  have h5 : UInt256.lor (UInt256.land (UInt256.ofNat 288230376151711744)
      (UInt256.shiftRight (tickLogSquareAt r 5) (UInt256.ofNat 197)))
      (tickLogAccRun r (tickLogInitial msb) 5) = tickLogAccRun r (tickLogInitial msb) 6 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 5 (by decide)
  have h6 : UInt256.lor (UInt256.land (UInt256.ofNat 144115188075855872)
      (UInt256.shiftRight (tickLogSquareAt r 6) (UInt256.ofNat 198)))
      (tickLogAccRun r (tickLogInitial msb) 6) = tickLogAccRun r (tickLogInitial msb) 7 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 6 (by decide)
  have h7 : UInt256.lor (UInt256.land (UInt256.ofNat 72057594037927936)
      (UInt256.shiftRight (tickLogSquareAt r 7) (UInt256.ofNat 199)))
      (tickLogAccRun r (tickLogInitial msb) 7) = tickLogAccRun r (tickLogInitial msb) 8 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 7 (by decide)
  have h8 : UInt256.lor (UInt256.land (UInt256.ofNat 36028797018963968)
      (UInt256.shiftRight (tickLogSquareAt r 8) (UInt256.ofNat 200)))
      (tickLogAccRun r (tickLogInitial msb) 8) = tickLogAccRun r (tickLogInitial msb) 9 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 8 (by decide)
  have h9 : UInt256.lor (UInt256.land (UInt256.ofNat 18014398509481984)
      (UInt256.shiftRight (tickLogSquareAt r 9) (UInt256.ofNat 201)))
      (tickLogAccRun r (tickLogInitial msb) 9) = tickLogAccRun r (tickLogInitial msb) 10 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 9 (by decide)
  have h10 : UInt256.lor (UInt256.land (UInt256.ofNat 9007199254740992)
      (UInt256.shiftRight (tickLogSquareAt r 10) (UInt256.ofNat 202)))
      (tickLogAccRun r (tickLogInitial msb) 10) = tickLogAccRun r (tickLogInitial msb) 11 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 10 (by decide)
  have h11 : UInt256.lor (UInt256.land (UInt256.ofNat 4503599627370496)
      (UInt256.shiftRight (tickLogSquareAt r 11) (UInt256.ofNat 203)))
      (tickLogAccRun r (tickLogInitial msb) 11) = tickLogAccRun r (tickLogInitial msb) 12 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 11 (by decide)
  unfold tickLogAccStack1 at rd
  have rout := uniswapV3Pool_block_14514 (immWords := wordsOf (immStore v)) (by evm_ov) rd
  refine ⟨k + 64, C + 192, ?_⟩
  simpa only [uniswapV3Pool_block_14514_stack, tickLogAccStack,
    h4, h5, h6, h7, h8, h9, h10, h11] using rout

theorem tickLogAccX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C msb : Nat} {aw r : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14273⟩
      (UInt256.ofNat msb :: r :: R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14638⟩
      (tickLogAccStack r msb R) mem aw rdata σ k' C' := by
  obtain ⟨k', C', r1⟩ := tickLogSquaresX rd hov
  obtain ⟨k'', C'', r2⟩ := tickLogAcc1X r1 hov
  exact tickLogAcc2X r2 (by omega)

end Benchmarks.UniswapV3.Pool
