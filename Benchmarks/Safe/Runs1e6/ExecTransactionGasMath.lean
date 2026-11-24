import Benchmarks.Safe.Runs1e6.ExecTransactionGasSource
import Benchmarks.Safe.Runs1e6.ExecGuardCallPrepare
import Benchmarks.Safe.Runs1e6.SafeAddTrace
import Benchmarks.Safe.Runs1e6.MaximumTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000 in
theorem safeExecRequiredGasTrace (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata src} {sigPtr guard hash : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4417⟩
      (execGuardSaved p src sigPtr guard hash R) mem aw rdata σ k C)
    (hov : R.length + 32 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬ ExecGasFits p.tx.safeTxGas) ∨
    ∃ k' C', ExecGasFits p.tx.safeTxGas ∧ RD fork safeBytecode I g s0 ⟨4465⟩
      (execRequiredGas p.tx.safeTxGas :: execGuardSaved p src sigPtr guard hash R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_4417 (by simp; omega) (by jump_dest) h
  by_cases hfirst : p.tx.safeTxGas.toNat + 2500 < UInt256.size
  swap
  · exact .inl ⟨safeCheckedAddOverflow h₁
      (by change UInt256.size ≤ p.tx.safeTxGas.toNat + 2500; omega)
      (by simp [execGuardSaved]; omega), fun hf ↦ hfirst hf.1⟩
  obtain ⟨_, _, h₂⟩ := safeCheckedAddTrace h₁ hfirst
    (by simp [execGuardSaved]; omega) (by jump_dest)
  have h₃ := safeRuntime_block_4432 (by simp; omega) (by jump_dest) h₂
  obtain ⟨_, _, h₄⟩ := safeCheckedDivTrace h₃ (by decide)
    (by simp [execGuardSaved]; omega) (by jump_dest)
  have h₅ := safeRuntime_block_4447 (by simp [execGuardSaved]; omega) (by jump_dest) h₄
  obtain ⟨_, _, h₆⟩ := safeMaximumTrace h₅
    (by simp [execGuardSaved]; omega) (by jump_dest)
  have h₇ := safeRuntime_block_4453 (by simp [execGuardSaved]; omega) (by jump_dest) h₆
  by_cases hsecond : (execGasMaximum p.tx.safeTxGas).toNat + 500 < UInt256.size
  swap
  · exact .inl ⟨safeCheckedAddOverflow h₇
      (by change UInt256.size ≤ (execGasMaximum p.tx.safeTxGas).toNat + 500; omega)
      (by simp [execGuardSaved]; omega), fun hf ↦ hsecond hf.2⟩
  obtain ⟨k', C', h₈⟩ := safeCheckedAddTrace h₇ hsecond
    (by simp [execGuardSaved]; omega) (by jump_dest)
  exact .inr ⟨k', C', ⟨hfirst, hsecond⟩, h₈⟩

end Benchmarks.Safe.Runs1e6
