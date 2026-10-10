import Benchmarks.UniswapV3.Pool.SwapAccountingSecond
import Benchmarks.UniswapV3.Pool.SwapAccountingMath
import Benchmarks.UniswapV3.Pool.SwapAccountingCalculatedTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapAccountingBranchX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3383⟩ else ⟨3445⟩)
      (q :: p :: R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstate : frame.locals.get? "state" = some s.value)
    (hstep : frame.locals.get? "step" = some d.value)
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hfit : s.Fits) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) (hb : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 9 ≤ 1024) :
    (ExecBlock config frame evm (swapAccountingBody exactInput) .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecBlock config frame evm (swapAccountingBody exactInput)
        (.ok (swapAccountingFrame frame exactInput s d) evm) ∧
      (swapAccountingState exactInput s d).Fits ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3504⟩ (q :: p :: R) mem' aw' rdata σ k' C' ∧
        HeapMemory mem' aw' free ∧ SwapStateMemory mem' p (swapAccountingState exactInput s d) ∧
        SwapIterationMemory mem' q d ∧ MemoryPrefix mem mem' p.toNat ∧ aw.toNat ≤ aw'.toNat) := by
  have hbody : swapAccountingBody exactInput = (swapAccountingBody exactInput).take 3 ++
      [(swapAccountingBody exactInput)[3]!, (swapAccountingBody exactInput)[4]!] := by
    cases exactInput <;> rfl
  rcases swapAccountingSecondX exactInput s d frame evm rd hf hstate hstep hm hs hd hp hdisj hb
      (by omega) with
    ⟨hex1, hr⟩ | ⟨hex1, hv, m1, a1, k1, C1, hC1, r1, hm1, hs1, hd1, hp1, hmono1⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [hbody]
    exact execBlock_append_term hex1 (by intro _ _ h; cases h)
  · let s1 : SwapStateData := {s with remaining := swapAccountingRemaining exactInput s d}
    rcases swapAccountingMathX exactInput s1 d (swapAccountingSecondFrame frame exactInput s d)
        evm r1 hf (swapAccountingSecondFrame_state frame exactInput s d)
        (swapAccountingSecondFrame_result frame exactInput s d) hm1 hs1 hfit.2.1 hv
        (by omega) hov with
      ⟨hex2, hr⟩ | ⟨hex2, a2, k2, C2, hC2, r2, hm2, hmono2⟩
    · refine Or.inl ⟨?_, hr⟩
      rw [hbody]
      exact execBlock_append_ok hex1 (ExecBlock.consRevert hex2)
    · have hex3 := swapAccountingCalculatedSource (evm := evm) exactInput s1
        (swapAccountingCalculated exactInput s d)
        (swapAccountingMathFrame_state frame exactInput s d)
        (swapAccountingMathFrame_result frame exactInput s d)
      obtain ⟨k3, C3, hC3, r3, hm3, hs3, hd3, hp3, hmono3⟩ :=
        swapAccountingCalculatedX exactInput s1 d (swapAccountingCalculated exactInput s d)
          r2 hm2 hs1 hd1 hp hdisj (by omega) (by omega)
      refine Or.inr ⟨?_, swapAccountingState_fits exactInput s d hfit,
        _, _, k3, C3, by omega, r3, hm3, hs3, hd3, hp1.trans hp3,
        hmono1.trans (hmono2.trans hmono3)⟩
      rw [hbody]
      exact execBlock_append_ok hex1 (ExecBlock.consNormal hex2 (ExecBlock.consNormal hex3 .nil))

theorem swapAccountingX {σ : AccountMap} {ee : ExecutionEnv} {g : Sat256}
    {s0 : EVM.State} {k C : Nat} {aw p q free : UInt256}
    {mem rdata : ByteArray} {R : List UInt256} {v : UniswapV3PoolImmutables}
    (exactInput : Bool) (s : SwapStateData) (d : SwapIterationData)
    (frame : Frame) (evm : EVM.State)
    (rd : RD (deployedRuntime v) ee g s0 (if exactInput then ⟨3383⟩ else ⟨3445⟩)
      (q :: p :: R) mem aw rdata σ k C)
    (hf : frame.contract = contract) (hstate : frame.locals.get? "state" = some s.value)
    (hstep : frame.locals.get? "step" = some d.value)
    (hexact : frame.locals.get? "exactInput" = some (.bool exactInput))
    (hm : HeapMemory mem aw free) (hs : SwapStateMemory mem p s)
    (hd : SwapIterationMemory mem q d) (hfit : s.Fits) (hp : 96 ≤ p.toNat)
    (hdisj : p.toNat + 224 ≤ q.toNat) (hb : q.toNat + 224 ≤ 2 ^ 200)
    (hov : R.length + 9 ≤ 1024) :
    (ExecStmt config frame evm swapLoopBody[13]! .reverted ∧
      (RDrev (deployedRuntime v) g s0 ∨ RDinvalid (deployedRuntime v) g s0)) ∨
    (ExecStmt config frame evm swapLoopBody[13]!
        (.ok (swapAccountingFrame frame exactInput s d) evm) ∧
      (swapAccountingState exactInput s d).Fits ∧
      ∃ mem' aw' k' C', C + 1 + (Cₘ aw' - Cₘ aw) ≤ C' ∧
        RD (deployedRuntime v) ee g s0 ⟨3504⟩ (q :: p :: R) mem' aw' rdata σ k' C' ∧
        HeapMemory mem' aw' free ∧ SwapStateMemory mem' p (swapAccountingState exactInput s d) ∧
        SwapIterationMemory mem' q d ∧ MemoryPrefix mem mem' p.toNat ∧ aw.toNat ≤ aw'.toNat) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hexact
  rcases swapAccountingBranchX exactInput s d frame evm rd hf hstate hstep hm hs hd hfit hp
      hdisj hb hov with ⟨hex, hr⟩ | ⟨hex, hgood⟩
  · refine Or.inl ⟨?_, hr⟩
    rw [swapAccountingStmt]
    cases exactInput
    · exact ExecStmt.iteFalse he hex
    · exact ExecStmt.iteTrue he hex
  · refine Or.inr ⟨?_, hgood⟩
    rw [swapAccountingStmt]
    cases exactInput
    · exact ExecStmt.iteFalse he hex
    · exact ExecStmt.iteTrue he hex

end Benchmarks.UniswapV3.Pool
