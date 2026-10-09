import Benchmarks.CompoundIII.Comet.InternalOutcome
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- GENERALIZES InternalOutcome to a routine that also returns proof-level data.
inductive InternalValueOutcome (α : Type) where
  | ok (evm : State) (value : α)
  | reverted
  | staticViolation

def InternalValueOutcome.ofOption {α : Type} : Option (State × α) → InternalValueOutcome α
  | none => .reverted
  | some (evm, value) => .ok evm value

def InternalValueOutcome.map {α β : Type} (f : α → β) :
    InternalValueOutcome α → InternalValueOutcome β
  | .ok evm value => .ok evm (f value)
  | .reverted => .reverted
  | .staticViolation => .staticViolation

def internalValueFrameResult {α : Type} (frame : α → Frame) :
    InternalValueOutcome α → ExecResult
  | .ok evm value => .ok (frame value) evm
  | .reverted => .reverted
  | .staticViolation => .staticViolation

-- GENERALIZES internalPreservingRun with return data, exact allocation growth, and a memory prefix.
def internalValuePreservingRun {α : Type} (code : ByteArray) (ee : ExecutionEnv) (g : Sat256)
    (s0 : State) (before : ByteArray) (free : UInt256) (growth : Nat) (ret : UInt256)
    (stack : α → List UInt256) : InternalValueOutcome α → Prop
  | .ok evm value => ∃ σ mem free' aw data k C,
      SourceState s0 ee σ evm ∧ free'.toNat = free.toNat + growth ∧
      memLoad ⟨64⟩ mem = free' ∧ free'.toNat ≤ mem.size ∧
      MemoryPrefix before mem free.toNat ∧ RD code ee g s0 ret (stack value) mem aw data σ k C
  | .reverted => RDrev code g s0
  | .staticViolation => RDstatic code g s0

end Benchmarks.CompoundIII.Comet
