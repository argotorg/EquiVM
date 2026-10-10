import Benchmarks.UniswapV3.Pool.SwapAccountingMathLoad
import Benchmarks.UniswapV3.Pool.SwapAccountingSource
import Benchmarks.UniswapV3.Pool.SafeArithmeticInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapAccountingMathX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3424⟩ else ⟨3487⟩)
      ([swapAccountingSecond exactInput d, (if exactInput then ⟨3435⟩ else ⟨3498⟩), q, p] ++ R)
      mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstate : frame.locals.get? "state" = some s.value)
    (hresult : frame.locals.get? (swapAccountingSecondName exactInput) =
      some (.int (Int.ofNat (swapAccountingSecond exactInput d).toNat)))
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hx : -(2 ^ 255 : Int) ≤ s.calculated ∧ s.calculated < 2 ^ 255)
    (hy : safeCast256Valid (swapAccountingSecond exactInput d))
    (hb : p.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 9 ≤ 1024) :
    (ExecStmt config frame evm (swapAccountingBody exactInput)[3]! .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config frame evm (swapAccountingBody exactInput)[3]!
        (.ok (resumeAfterInternalCall frame (swapAccountingResultName exactInput)
          (some [.int (swapAccountingCalculated exactInput s d)])) evm) ∧
      ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3435⟩ else ⟨3498⟩)
          (EVM.wordOfInt (swapAccountingCalculated exactInput s d) :: q :: p :: R)
          mem aw' rdata σ k' C' ∧ HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat) := by
  obtain ⟨a1, k1, C1, hC1, r1, hm1, hmono⟩ :=
    swapAccountingMathLoadX exactInput s rd hm hs hb (by omega)
  have he := evalSwapAccountingMathArgs (evm := evm) exactInput s d hstate hresult
  have hylo : -(2 ^ 255 : Int) ≤ Int.ofNat (swapAccountingSecond exactInput d).toNat := by
    rw [Int.ofNat_eq_natCast]
    omega
  have hyhi : Int.ofNat (swapAccountingSecond exactInput d).toNat < (2 ^ 255 : Int) := by
    dsimp only [safeCast256Valid] at hy
    rw [Int.ofNat_eq_natCast]
    exact_mod_cast hy
  rcases safeSignedMathInternalMonoX (v := v) exactInput s.calculated
      (Int.ofNat (swapAccountingSecond exactInput d).toNat) frame evm
      (swapAccountingMathArgs exactInput) (swapAccountingResultName exactInput) hf he
      (by simpa only [wordOfInt_ofNat_toNat] using r1) hx.1 hx.2 hylo hyhi
      (by cases exactInput <;> rw [uniswapV3PoolPatchedValidJumps v] <;> native_decide)
      (by change R.length + 2 + 7 ≤ 1024; omega) with
    ⟨hex, hr⟩ | ⟨hex, _, k2, C2, hC2, r2⟩
  · exact Or.inl ⟨by rw [swapAccountingMathStmt]; exact hex, hr⟩
  · refine Or.inr ⟨?_, a1, k2, C2, by omega, r2, hm1, hmono⟩
    rw [swapAccountingMathStmt]
    exact hex

end Benchmarks.UniswapV3.Pool
