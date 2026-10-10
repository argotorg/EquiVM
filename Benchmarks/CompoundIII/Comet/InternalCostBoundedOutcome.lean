import Benchmarks.CompoundIII.Comet.InternalBoundedOutcome
import Benchmarks.CompoundIII.Comet.RemainingGas

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalBoundedRun by retaining a lower bound on consumed gas.
def internalCostBoundedRun (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (spent lower upper : Nat) (ret : UInt256) (R : List UInt256) : InternalOutcome → Prop
  | .ok evm => ∃ σ mem free aw data k C,
      SourceState s0 ee σ evm ∧ lower ≤ free.toNat ∧ free.toNat ≤ upper ∧
      memLoad ⟨64⟩ mem = free ∧ free.toNat ≤ mem.size ∧ spent ≤ C ∧
      RD code ee g s0 ret R mem aw data σ k C
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0

theorem internalBoundedRun.fromRemaining {code ee g s0 C s lower upper ret R result}
    (hr : internalBoundedRun code ee (g.subNat C) s lower upper ret R result)
    (hbase : RunRemainder code ee g s0 C s) :
    internalCostBoundedRun code ee g s0 C lower upper ret R result := by
  cases result with
  | reverted => exact hbase.revert hr
  | staticViolation => exact hbase.staticViolation hr
  | ok evm =>
      obtain ⟨σ, mem, free, aw, data, k', C', hs, hl, hu, hf, hm, hrd⟩ := hr
      exact ⟨σ, mem, free, aw, data, C + k', C + C', hbase.sourceOut hs,
        hl, hu, hf, hm, by omega, hbase.compose hrd⟩

end Benchmarks.CompoundIII.Comet
