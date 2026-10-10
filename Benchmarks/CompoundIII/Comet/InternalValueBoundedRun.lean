import Benchmarks.CompoundIII.Comet.InternalValueOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalValuePreservingRun to an upper bound on allocation growth.
def internalValueBoundedRun {α : Type} (code : ByteArray) (ee : ExecutionEnv) (g : Sat256)
    (s0 : State) (before : ByteArray) (free : UInt256) (budget : Nat) (ret : UInt256)
    (stack : α → List UInt256) (result : InternalValueOutcome α) : Prop :=
  ∃ growth, growth ≤ budget ∧
    internalValuePreservingRun code ee g s0 before free growth ret stack result

theorem internalValueBoundedRun.mono {α code ee g s0 before free budget budget' ret stack}
    {result : InternalValueOutcome α}
    (h : internalValueBoundedRun code ee g s0 before free budget ret stack result)
    (hle : budget ≤ budget') :
    internalValueBoundedRun code ee g s0 before free budget' ret stack result := by
  obtain ⟨growth, hb, hr⟩ := h
  exact ⟨growth, le_trans hb hle, hr⟩

-- LIBRARY CANDIDATE: compose a preserved memory prefix and exact initial allocation growth.
theorem internalValueBoundedRun.prepend {α code ee g s0 before middle free free' budget step ret stack}
    {result : InternalValueOutcome α}
    (h : internalValueBoundedRun code ee g s0 middle free' budget ret stack result)
    (hp : MemoryPrefix before middle free.toNat) (hf : free'.toNat = free.toNat + step) :
    internalValueBoundedRun code ee g s0 before free (step + budget) ret stack result := by
  obtain ⟨growth, hb, hr⟩ := h
  refine ⟨step + growth, by omega, ?_⟩
  cases result with
  | reverted => exact hr
  | staticViolation => exact hr
  | ok evm value =>
      obtain ⟨σ, mem, last, aw, data, k, C, hs, hlast, hfree, hsize, hprefix, hrd⟩ := hr
      exact ⟨σ, mem, last, aw, data, k, C, hs, by omega, hfree, hsize,
        hp.trans (hprefix.mono (by omega)), hrd⟩

end Benchmarks.CompoundIII.Comet
