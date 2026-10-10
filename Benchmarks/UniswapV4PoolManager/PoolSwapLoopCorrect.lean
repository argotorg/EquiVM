import Benchmarks.UniswapV4PoolManager.PoolSwapIterationCorrect
import Benchmarks.UniswapV4PoolManager.PoolSwapLoopConditionTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem PoolSwapActiveWords.condition {aw step state params : UInt256}
    (h : PoolSwapActiveWords aw step state params) (remaining : UInt256) :
    poolSwapConditionAW aw state params remaining = aw := by
  simp only [poolSwapConditionAW, h.state_base, h.params_word (by decide : 96+32 ≤ 160), ite_self]

def poolSwapLoopExit (v : PoolManagerImmutables) (I : ExecutionEnv) (g : Sat256) (s0 : State)
    (rdata : ByteArray) (p : PoolSwapParamsWords) (id step state params x1 tag fee protocol : UInt256)
    (R : List UInt256) (aw : UInt256) (C : Nat) (initialFrame : Frame) (initialMem : ByteArray) (ff : Frame) (post : State) : Prop :=
  ∃ q' mem' aw' k' C', C ≤ C' ∧ post.executionEnv = I ∧ post.σ₀ = s0.σ₀ ∧
    RD (deployedRuntime v) I g s0 ⟨21536⟩
      (poolSwapLoopStack q' p id step state params x1 tag fee protocol R) mem' aw' rdata post.accountMap k' C' ∧
    PoolSwapLoopInvariant ff mem' id step state params fee protocol p q' ∧ ¬poolSwapLoopContinues p q' ∧
    MemoryWindowEq initialMem mem' 64 (min step.toNat state.toNat) ∧ PoolSwapSavedLocals initialFrame ff ∧
    (PoolSwapActiveWords aw step state params → aw' = aw)

theorem poolSwapLoopFuel {I : ExecutionEnv} {g : Sat256} {s0 : State} {rdata : ByteArray}
    {p : PoolSwapParamsWords} {step state params id tag x1 fee protocol : UInt256} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024)
    (hspacing : int24Canonical p.tickSpacing) (hlimit : p.priceLimit.toNat < 2^160)
    (hfee : fee.toNat < 2^24) (hprotocol : protocol.toNat < 2^16) (fuel : Nat) :
    ∀ (f : Frame) (evm : State) (mem : ByteArray) (aw : UInt256) (q : PoolSwapLoopWords) (k C : Nat),
      g.toNat-C = fuel → evm.executionEnv = I → evm.σ₀ = s0.σ₀ →
      PoolSwapLoopInvariant f mem id step state params fee protocol p q →
      RD (deployedRuntime v) I g s0 ⟨19155⟩
        (poolSwapLoopStack q p id step state params x1 tag fee protocol R) mem aw rdata evm.accountMap k C →
      X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
      ∃ result, ExecStmt config f evm (.while poolSwapLoopCondition poolSwapLoopBody) result ∧
        blockResultTrace (deployedRuntime v) g s0
          (poolSwapLoopExit v I g s0 rdata p id step state params x1 tag fee protocol R aw C f mem)
          (fun _ _ => False) result := by
  induction fuel using Nat.strong_induction_on with
  | h fuel ih =>
    intro f evm mem aw q k C hmeasure hI hσ0 hinv h
    by_cases hover : g.toNat < C
    · exact .inl (h.oog_of_cost_gt hover)
    obtain ⟨k1, C1, hC1, rd1⟩ := poolSwapLoopConditionTrace v (by omega) hinv.memory hinv.price hlimit h
    have hcond := poolSwapLoopCondition_eval (evm := evm) hinv.locals
    by_cases hgo : poolSwapLoopContinues p q
    · rw [if_pos hgo] at rd1
      rw [decide_eq_true hgo] at hcond
      obtain ⟨bodyResult, hbody, hbodyTrace⟩ := poolSwapIterationCorrect v hstack hI hinv
        hspacing hlimit hfee hprotocol rd1
      cases bodyResult with
      | ok ff post =>
        obtain ⟨q2, mem2, aw2, k2, C2, hC2, hI2, hσ2, rd2, hinv2, hw2, hs2, ha2⟩ := hbodyTrace
        by_cases hover2 : g.toNat < C2
        · exact .inl (rd2.oog_of_cost_gt hover2)
        have hless : g.toNat-C2 < fuel := by omega
        rcases ih (g.toNat-C2) hless ff post mem2 aw2 q2 k2 C2 rfl hI2 (hσ2.trans hσ0) hinv2 rd2 with hog | ⟨result, hs, ht⟩
        · exact .inl hog
        · refine .inr ⟨result, ExecStmt.whileTrue hcond hbody hs, ?_⟩
          apply blockResultTrace_mono ht
          intro last lastPost _ hlast
          obtain ⟨q3, mem3, aw3, k3, C3, hC3, hI3, hσ3, rd3, hinv3, hstop, hw3, hs3, ha3⟩ := hlast
          refine ⟨q3, mem3, aw3, k3, C3, by omega, hI3, hσ3, rd3, hinv3, hstop,
            hw2.trans hw3, hs2.trans hs3, ?_⟩
          intro ha
          have hcond := ha.condition q.remaining
          have h2 : aw2 = aw := (ha2 (by rw [hcond]; exact ha)).trans hcond
          exact (ha3 (by rw [h2]; exact ha)).trans h2
      | reverted => exact .inr ⟨.reverted, ExecStmt.whileRevert hcond hbody, hbodyTrace⟩
      | staticViolation => exact .inr ⟨.staticViolation, ExecStmt.whileStatic hcond hbody, hbodyTrace⟩
      | returned | «break» | «continue» => exact False.elim hbodyTrace
    · rw [if_neg hgo] at rd1
      rw [decide_eq_false hgo] at hcond
      exact .inr ⟨.ok f evm, ExecStmt.whileFalse hcond,
        q, mem, _, k1, C1, hC1, hI, hσ0, rd1, hinv, hgo, hinv.memory.window_refl,
        PoolSwapSavedLocals.refl f, fun ha => ha.condition q.remaining⟩

theorem poolSwapLoopCorrect {I : ExecutionEnv} {g : Sat256} {s0 evm : State} {f : Frame}
    {mem rdata : ByteArray} {p : PoolSwapParamsWords} {q : PoolSwapLoopWords}
    {aw step state params id tag x1 fee protocol : UInt256} {k C : Nat} {R : List UInt256}
    (v : PoolManagerImmutables) (hstack : R.length+36 ≤ 1024) (hI : evm.executionEnv = I)
    (hσ0 : evm.σ₀ = s0.σ₀)
    (hinv : PoolSwapLoopInvariant f mem id step state params fee protocol p q)
    (hspacing : int24Canonical p.tickSpacing) (hlimit : p.priceLimit.toNat < 2^160)
    (hfee : fee.toNat < 2^24) (hprotocol : protocol.toNat < 2^16)
    (h : RD (deployedRuntime v) I g s0 ⟨19155⟩
      (poolSwapLoopStack q p id step state params x1 tag fee protocol R) mem aw rdata evm.accountMap k C) :
    X (g.toNat+1) (D_J (deployedRuntime v) 0) s0 = .error .OutOfGass ∨
    ∃ result, ExecStmt config f evm poolSwapFunction.body[28]! result ∧
      blockResultTrace (deployedRuntime v) g s0
        (poolSwapLoopExit v I g s0 rdata p id step state params x1 tag fee protocol R aw C f mem)
        (fun _ _ => False) result := by
  rw [poolSwapFunction_loop]
  exact poolSwapLoopFuel v hstack hspacing hlimit hfee hprotocol (g.toNat-C) f evm mem aw q k C rfl hI hσ0 hinv h

end Benchmarks.UniswapV4PoolManager
