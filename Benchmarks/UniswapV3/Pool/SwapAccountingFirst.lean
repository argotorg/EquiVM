import Benchmarks.UniswapV3.Pool.SwapAccountingFirstLoad
import Benchmarks.UniswapV3.Pool.SwapAccountingSource
import Benchmarks.UniswapV3.Pool.SafeArithmeticInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapAccountingFirstX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (d : SwapIterationData) (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3383⟩ else ⟨3445⟩)
      (q :: R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstep : frame.locals.get? "step" = some d.value)
    (hm : HeapMemory mem aw free) (hd : SwapIterationMemory mem q d)
    (hb : q.toNat + 224 ≤ 2 ^ 200) (hov : R.length + 6 ≤ 1024) :
    (ExecStmt config frame evm (swapAccountingBody exactInput)[0]! .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config frame evm (swapAccountingBody exactInput)[0]!
        (.ok (swapAccountingFirstFrame frame exactInput d) evm) ∧
      safeCast256Valid (swapAccountingFirst exactInput d) ∧
      ∃ aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3401⟩ else ⟨3458⟩)
          (swapAccountingFirst exactInput d :: q :: R) mem aw' rdata σ k' C' ∧
        HeapMemory mem aw' free ∧ aw.toNat ≤ aw'.toNat) := by
  obtain ⟨a1, k1, C1, hC1, r1, hm1, hmono⟩ :=
    swapAccountingFirstLoadX exactInput d rd hm hd hb (by omega)
  have he := evalSwapAccountingFirstArgs (evm := evm) exactInput d hstep
  rcases safeCast256InternalMonoX (v := v) (swapAccountingFirst exactInput d) frame evm
      (swapAccountingFirstArgs exactInput) (swapAccountingFirstName exactInput) hf he r1
      (by cases exactInput <;> rw [uniswapV3PoolPatchedValidJumps v] <;> native_decide)
      (by change R.length + 1 + 5 ≤ 1024; omega) with
    ⟨hex, hr⟩ | ⟨hex, hv, k2, C2, hC2, r2⟩
  · exact Or.inl ⟨by rw [swapAccountingFirstStmt]; exact hex, hr⟩
  · refine Or.inr ⟨?_, hv, a1, k2, C2, by omega, r2, hm1, hmono⟩
    rw [swapAccountingFirstStmt]
    exact hex

end Benchmarks.UniswapV3.Pool
