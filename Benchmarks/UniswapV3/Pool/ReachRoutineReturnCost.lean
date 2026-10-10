import Benchmarks.UniswapV3.Pool.ReachRoutineCost

open Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: keep the caller's cost when a total routine returns at a fixed cursor.
theorem rdRoutine_return_mono {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : EVM.State}
    {pc pc' aw aw' : UInt256} {stack stack' : List UInt256} {mem mem' rdata rdata' : ByteArray}
    {σ σ' : AccountMap} {k C : Nat}
    (rd : RD code ee g s0 pc stack mem aw rdata σ k C)
    (run : ∀ (gas : Sat256) (start : EVM.State),
      RD code ee gas start pc stack mem aw rdata σ 0 0 →
        ∃ k' C', RD code ee gas start pc' stack' mem' aw' rdata' σ' k' C') :
    ∃ k' C', C ≤ C' ∧ RD code ee g s0 pc' stack' mem' aw' rdata' σ' k' C' := by
  have h := rdRoutine_mono (valid := True) rd
    (fun gas start rr ↦ Or.inr ⟨trivial, run gas start rr⟩)
  exact (h.resolve_left (fun hb ↦ hb.1 trivial)).2

end Benchmarks.UniswapV3.Pool
