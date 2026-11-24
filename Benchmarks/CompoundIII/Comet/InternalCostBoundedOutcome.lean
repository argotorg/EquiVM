import Benchmarks.CompoundIII.Comet.InternalBoundedOutcome
import Benchmarks.CompoundIII.Comet.RemainingGas

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES internalBoundedRun by retaining a lower bound on consumed gas.
def internalCostBoundedRun (fork : Ethereum.Fork) (code : ByteArray) (ee : ExecutionEnv) (g : Sat256) (s0 : State)
    (spent lower upper : Nat) (ret : UInt256) (R : List UInt256) : InternalOutcome → Prop
  | .ok evm => ∃ σ mem free aw data k C,
      SourceState s0 ee σ evm ∧ lower ≤ free.toNat ∧ free.toNat ≤ upper ∧
      memLoad ⟨64⟩ mem = free ∧ free.toNat ≤ mem.size ∧ spent ≤ C ∧
      RD fork code ee g s0 ret R mem aw data σ k C
  | .reverted => RDrev fork code g s0
  | .staticViolation => RDstatic fork code g s0

theorem internalBoundedRun.fromRemaining {code ee g s0 C s lower upper ret R result}
    (hr : internalBoundedRun fork code ee (g.subNat C) s lower upper ret R result)
    (hbase : RunRemainder fork code ee g s0 C s) :
    internalCostBoundedRun fork code ee g s0 C lower upper ret R result := by
  cases result with
  | reverted => exact hbase.revert hr
  | staticViolation => exact hbase.staticViolation hr
  | ok evm =>
      obtain ⟨σ, mem, free, aw, data, k', C', hs, hl, hu, hf, hm, hrd⟩ := hr
      exact ⟨σ, mem, free, aw, data, C + k', C + C', hbase.sourceOut hs,
        hl, hu, hf, hm, by omega, hbase.compose hrd⟩

end Benchmarks.CompoundIII.Comet
