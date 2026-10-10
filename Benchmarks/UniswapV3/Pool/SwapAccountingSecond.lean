import Benchmarks.UniswapV3.Pool.SwapAccountingFirst
import Benchmarks.UniswapV3.Pool.SwapAccountingRemainingTrace
import Benchmarks.UniswapV3.Pool.SwapAccountingFrameLaws

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapAccountingSecondX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3383⟩ else ⟨3445⟩)
      (q :: p :: R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstate : frame.locals.get? "state" = some s.value)
    (hstep : frame.locals.get? "step" = some d.value)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) (hb : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 8 ≤ 1024) :
    (ExecBlock config frame evm ((swapAccountingBody exactInput).take 3) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm ((swapAccountingBody exactInput).take 3)
        (.ok (swapAccountingSecondFrame frame exactInput s d) evm) ∧
      safeCast256Valid (swapAccountingSecond exactInput d) ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3424⟩ else ⟨3487⟩)
          ([swapAccountingSecond exactInput d, (if exactInput then ⟨3435⟩ else ⟨3498⟩), q, p] ++ R)
          mem' aw' rdata σ k' C' ∧ HeapMemory mem' aw' free ∧
        SwapStateMemory mem' p {s with remaining := swapAccountingRemaining exactInput s d} ∧
        SwapIterationMemory mem' q d ∧ MemoryPrefix mem mem' p.toNat ∧ aw.toNat ≤ aw'.toNat) := by
  have hbody : (swapAccountingBody exactInput).take 3 =
      [(swapAccountingBody exactInput)[0]!, (swapAccountingBody exactInput)[1]!,
        (swapAccountingBody exactInput)[2]!] := by cases exactInput <;> rfl
  rcases swapAccountingFirstX exactInput d frame evm rd hf hstep hm hd hb
      (by change R.length + 1 + 6 ≤ 1024; omega) with
    ⟨hex1, hr⟩ | ⟨hex1, _, a1, k1, C1, hC1, r1, hm1, hmono1⟩
  · exact Or.inl ⟨by rw [hbody]; exact ExecBlock.consRevert hex1, hr⟩
  · have hg := (swapAccountingFirstFrame_get frame exactInput d "state"
      (by cases exactInput <;> decide)).trans hstate
    have hex2 := swapAccountingRemainingSource (evm := evm) exactInput s d hg
      (swapAccountingFirstFrame_result frame exactInput d)
    obtain ⟨a2, k2, C2, hC2, r2, hm2, hs2, hd2, hp2, hmono2⟩ :=
      swapAccountingRemainingX exactInput s d r1 hm1 hs hd hp hdisj hb (by omega)
    have he := evalSwapAccountingSecondArgs (evm := evm) exactInput d
      (swapAccountingRemainingFrame_step exactInput s d hstep)
    rcases safeCast256InternalMonoX (v := v) (swapAccountingSecond exactInput d)
        (swapAccountingRemainingFrame frame exactInput s d) evm
        (swapAccountingSecondArgs exactInput)
        (swapAccountingSecondName exactInput) hf he r2
        (by cases exactInput <;> rw [uniswapV3PoolPatchedValidJumps v] <;> native_decide)
        (by change R.length + 3 + 5 ≤ 1024; omega) with
      ⟨hex3, hr⟩ | ⟨hex3, hv, k3, C3, hC3, r3⟩
    · refine Or.inl ⟨?_, hr⟩
      rw [hbody]
      refine ExecBlock.consNormal hex1 (ExecBlock.consNormal hex2 (ExecBlock.consRevert ?_))
      rw [swapAccountingSecondStmt]
      exact hex3
    · refine Or.inr ⟨?_, hv, _, a2, k3, C3, by omega, r3, hm2, hs2, hd2, hp2,
        hmono1.trans hmono2⟩
      rw [hbody]
      refine ExecBlock.consNormal hex1
        (ExecBlock.consNormal hex2 (ExecBlock.consNormal ?_ ExecBlock.nil))
      rw [swapAccountingSecondStmt]
      exact hex3

end Benchmarks.UniswapV3.Pool
