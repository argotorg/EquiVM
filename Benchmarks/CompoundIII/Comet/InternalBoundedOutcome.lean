import Benchmarks.CompoundIII.Comet.InternalPreservingOutcome

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalDynamicRun with lower and upper bounds on the returned free pointer.
def internalBoundedRun (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (lower upper : Nat) (ret : UInt256) (R : List UInt256) : InternalOutcome → Prop
  | .ok evm => ∃ σ mem free aw data k C,
      SourceState s0 ee σ evm ∧ lower ≤ free.toNat ∧ free.toNat ≤ upper ∧
      memLoad ⟨64⟩ mem = free ∧ free.toNat ≤ mem.size ∧ RD code ee g s0 ret R mem aw data σ k C
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0

theorem internalBoundedRun.mono {code ee g s0 lower upper lower' upper' ret R result}
    (hr : internalBoundedRun code ee g s0 lower upper ret R result)
    (hlo : lower' ≤ lower) (hhi : upper ≤ upper') :
    internalBoundedRun code ee g s0 lower' upper' ret R result := by
  cases result with
  | reverted => exact hr
  | staticViolation => exact hr
  | ok evm =>
      obtain ⟨σ, mem, free, aw, data, k, C, hs, hl, hu, hf, hm, hrd⟩ := hr
      exact ⟨σ, mem, free, aw, data, k, C, hs, le_trans hlo hl, le_trans hu hhi, hf, hm, hrd⟩

theorem internalPreservingRun.bounded {code ee g s0 before free data ret R result lower upper}
    (hr : internalPreservingRun code ee g s0 before free data ret R result)
    (hlo : lower ≤ free.toNat) (hhi : free.toNat ≤ upper) (hm : free.toNat ≤ before.size) :
    internalBoundedRun code ee g s0 lower upper ret R result := by
  cases result with
  | reverted => exact hr
  | staticViolation => exact hr
  | ok evm =>
      obtain ⟨mem, σ, aw, k, C, hs, hrd, hf, hsize⟩ := hr
      exact ⟨σ, mem, free, aw, data, k, C, hs, hlo, hhi, hf, le_trans hm hsize, hrd⟩

end Benchmarks.CompoundIII.Comet
