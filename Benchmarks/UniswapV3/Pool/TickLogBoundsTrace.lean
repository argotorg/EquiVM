import Benchmarks.UniswapV3.Pool.TickLogAccTrace
import Benchmarks.UniswapV3.Pool.TickLogBoundsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
open uniswapV3PoolBlocks
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def tickLogBoundsStack (log : UInt256) (R : List UInt256) : List UInt256 :=
  tickLogHighRaw log :: tickLogLowRaw log :: tickLogScaledLog log :: log :: R

theorem tickLogBoundsCompareX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw x0 x1 x2 x3 log : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14638⟩ (x0 :: x1 :: x2 :: x3 :: R)
      mem aw rdata σ k C)
    (hlog : UInt256.lor (UInt256.land (UInt256.ofNat 1125899906842624)
      (UInt256.shiftRight x3 (UInt256.ofNat 205)))
      (UInt256.lor (UInt256.land (UInt256.ofNat 2251799813685248)
        (UInt256.shiftRight x1 x2)) x0) = log)
    (hov : R.length + 7 ≤ 1024) :
    (tickLogLow log = tickLogHigh log ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14788⟩
      (tickLogLowRaw log :: tickLogBoundsStack log R) mem aw rdata σ k' C') ∨
    (tickLogLow log ≠ tickLogHigh log ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14740⟩
      (tickLogBoundsStack log R) mem aw rdata σ k' C') := by
  have hscaled : UInt256.mul log (UInt256.ofNat 255738958999603826347141) =
      tickLogScaledLog log := rfl
  have hhigh : UInt256.sar (UInt256.ofNat 128)
      (tickLogScaledLog log + UInt256.ofNat 291339464771989622907027621153398088495) =
      tickLogHighRaw log := rfl
  by_cases he : tickLogLow log = tickLogHigh log
  · have hw : UInt256.signextend (UInt256.ofNat 2) (tickLogLowRaw log) =
        UInt256.signextend (UInt256.ofNat 2) (tickLogHighRaw log) :=
      (tickLogSignextend_eq _ _).mpr he
    have rdBounds := uniswapV3Pool_block_14638_taken (immWords := wordsOf (immStore v)) hov
      (by
        rw [hlog]
        change UInt256.eq
          (UInt256.signextend (UInt256.ofNat 2) (UInt256.sar (UInt256.ofNat 128)
            (tickLogScaledLog log + UInt256.lnot (UInt256.ofNat 3402992956809132418596140100660247209))))
          (UInt256.signextend (UInt256.ofNat 2) (tickLogHighRaw log)) ≠ UInt256.ofNat 0
        rw [tickLogLowRaw_compiled, hw, uInt256_eq_self]
        decide)
      (by rw [uniswapV3PoolPatchedValidJumpsRuntime v]; jump_dest) rd
    have rb : RD (deployedRuntime v) ee g s0 ⟨14786⟩ (tickLogBoundsStack log R)
        mem aw rdata σ (k + 41) (C + 136) := by
      simpa only [uniswapV3Pool_block_14638_taken_stack, hlog, hscaled,
        tickLogLowRaw_compiled, tickLogBoundsStack, hhigh] using rdBounds
    unfold tickLogBoundsStack at rb
    have out := uniswapV3Pool_block_14786 (immWords := wordsOf (immStore v)) (by evm_ov) rb
    exact Or.inl ⟨he, _, _, out⟩
  · have hw : UInt256.eq (UInt256.signextend (UInt256.ofNat 2) (tickLogLowRaw log))
        (UInt256.signextend (UInt256.ofNat 2) (tickLogHighRaw log)) = ⟨0⟩ := by
      apply uInt256_eq_zero_of_ne
      intro h
      exact he ((tickLogSignextend_eq _ _).mp (uInt256_eq_one_eq h))
    have rdBounds := uniswapV3Pool_block_14638_fallthrough (immWords := wordsOf (immStore v)) hov
      (by
        rw [hlog]
        change UInt256.eq
          (UInt256.signextend (UInt256.ofNat 2) (UInt256.sar (UInt256.ofNat 128)
            (tickLogScaledLog log + UInt256.lnot (UInt256.ofNat 3402992956809132418596140100660247209))))
          (UInt256.signextend (UInt256.ofNat 2) (tickLogHighRaw log)) = UInt256.ofNat 0
        rw [tickLogLowRaw_compiled]
        exact hw) rd
    refine Or.inr ⟨he, k + 41, C + 136, ?_⟩
    simpa only [uniswapV3Pool_block_14638_fallthrough_stack, hlog, hscaled,
      tickLogLowRaw_compiled, tickLogBoundsStack, hhigh] using rdBounds

theorem tickLogBoundsX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C msb : Nat} {aw r : UInt256} {mem rdata : ByteArray}
    {R : List UInt256} {v : UniswapV3PoolImmutables}
    (rd : RD (deployedRuntime v) ee g s0 ⟨14638⟩ (tickLogAccStack r msb R)
      mem aw rdata σ k C) (hov : R.length + 9 ≤ 1024) :
    let log := tickLogAccRun r (tickLogInitial msb) 14
    let tail := UInt256.ofNat msb :: tickLogScaled (tickLogRun r 13) :: R
    (tickLogLow log = tickLogHigh log ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14788⟩
      (tickLogLowRaw log :: tickLogBoundsStack log tail) mem aw rdata σ k' C') ∨
    (tickLogLow log ≠ tickLogHigh log ∧ ∃ k' C', RD (deployedRuntime v) ee g s0 ⟨14740⟩
      (tickLogBoundsStack log tail) mem aw rdata σ k' C') := by
  have h12 : UInt256.lor (UInt256.land (UInt256.ofNat 2251799813685248)
      (UInt256.shiftRight (tickLogSquareAt r 12) ⟨204⟩))
      (tickLogAccRun r (tickLogInitial msb) 12) = tickLogAccRun r (tickLogInitial msb) 13 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 12 (by decide)
  have h13 : UInt256.lor (UInt256.land (UInt256.ofNat 1125899906842624)
      (UInt256.shiftRight (tickLogSquareAt r 13) (UInt256.ofNat 205)))
      (tickLogAccRun r (tickLogInitial msb) 13) = tickLogAccRun r (tickLogInitial msb) 14 :=
    tickLogAccRun_mask_step r (tickLogInitial msb) 13 (by decide)
  exact tickLogBoundsCompareX rd (by rw [h12, h13]) (by simp only [List.length_cons]; omega)

end Benchmarks.UniswapV3.Pool
