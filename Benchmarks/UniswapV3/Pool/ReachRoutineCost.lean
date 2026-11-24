import Benchmarks.UniswapV3.Pool.ReachLocal

variable {fork : Ethereum.Fork}

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a universally quantified routine can retain the caller's cost bound.
theorem rdRoutine_mono {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {pc pc' aw aw' : UInt256} {stack stack' : List UInt256} {mem mem' rdata rdata' : ByteArray}
    {σ σ' : AccountMap} {k C : Nat} {valid : Prop}
    (rd : RD fork code ee g s0 pc stack mem aw rdata σ k C)
    (run : ∀ (gas : Sat256) (start : EVM.State),
      RD fork code ee gas start pc stack mem aw rdata σ 0 0 →
        (¬valid ∧ (RDrev fork code gas start ∨ RDinvalid fork code gas start)) ∨
        (valid ∧ ∃ k' C', RD fork code ee gas start pc' stack' mem' aw' rdata' σ' k' C')) :
    (¬valid ∧ (RDrev fork code g s0 ∨ RDinvalid fork code g s0)) ∨
      (valid ∧ ∃ k' C', C ≤ C' ∧ RD fork code ee g s0 pc' stack' mem' aw' rdata' σ' k' C') := by
  classical
  rcases rdLocalize rd with hoog | ⟨start, hworld, hC, hx, rlocal⟩
  · by_cases hv : valid
    · exact Or.inr ⟨hv, C, C, Nat.le_refl C, Or.inl hoog⟩
    · exact Or.inl ⟨hv, Or.inl (Or.inl hoog)⟩
  · rcases run (g.subNat C) start rlocal with ⟨hb, hr⟩ | ⟨hv, kr, Cr, rr⟩
    · refine Or.inl ⟨hb, ?_⟩
      simpa only [RDrev, RDinvalid, ← hx] using hr
    · exact Or.inr ⟨hv, C + kr, C + Cr, by omega, rdGlobalize hworld hC hx rr⟩

end Benchmarks.UniswapV3.Pool
