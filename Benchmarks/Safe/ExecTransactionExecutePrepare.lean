import Benchmarks.Safe.ExecTransactionAllocate
import Benchmarks.Safe.ExecTransactionExecuteSource
import Benchmarks.Safe.CheckedSubtract

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecExecutePrepare (p : ExecTransactionInput)
    {I g s0 σ k C aw mem rdata src ptr} {before sigPtr guard hash : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3904⟩
      (execAllocatedStack p src ptr before sigPtr guard hash R) mem aw rdata σ k C)
    (hov : R.length + 36 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ p.tx.gasPrice = ⟨0⟩ ∧
      ∃ gasLeft : UInt256, gasLeft.toNat < 2500) ∨
    ∃ gasLeft k' C', (p.tx.gasPrice = ⟨0⟩ → 2500 ≤ gasLeft.toNat) ∧
      RD safeBytecode I g s0 ⟨7408⟩
        ([execCallGas p gasLeft, p.tx.operation, UInt256.ofNat ptr, p.tx.value,
          UInt256.ofNat p.tx.target.val, ⟨3940⟩, before] ++
          execGuardSaved p src sigPtr guard hash R) mem aw rdata σ k' C' := by
  by_cases hz : p.tx.gasPrice = ⟨0⟩
  · have h₁ := safeRuntime_block_3904_taken (by simp [execAllocatedStack, execGuardSaved]; omega)
      (by rw [hz]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_3921 (by
      simp [safeRuntime_block_3904_taken_stack, execGuardSaved]; omega) (by jump_dest) h₁
    let gasLeft := (g.subNat (C + 32 + 4 + 2)).toUInt256
    change RD safeBytecode I g s0 _
      (gasLeft :: ⟨2500⟩ :: ⟨3935⟩ :: p.tx.operation :: UInt256.ofNat ptr :: p.tx.value ::
        UInt256.ofNat p.tx.target.val :: ⟨3940⟩ :: before ::
          execGuardSaved p src sigPtr guard hash R) _ _ _ _ _ _ at h₂
    by_cases hfit : 2500 ≤ gasLeft.toNat
    swap
    · exact .inl ⟨safeSubtractUnderflow h₂ (by simp [execGuardSaved]; omega)
        (by change gasLeft.toNat < 2500; omega), hz, gasLeft, by omega⟩
    obtain ⟨k₃, C₃, h₃⟩ := safeSubtractTrace h₂ (by simp [execGuardSaved]; omega)
      hfit (by jump_dest)
    have h₄ := safeRuntime_block_3935 (by simp [execGuardSaved]; omega) (by jump_dest) h₃
    refine .inr ⟨gasLeft, k₃ + 3, C₃ + 12, fun _ ↦ hfit, ?_⟩
    simpa only [execCallGas, if_pos hz] using h₄
  · have heq : UInt256.eq ⟨0⟩ p.tx.gasPrice = ⟨0⟩ := by
      rw [uInt256_eq_comm]
      exact u256_eq_of_ne hz
    have h₁ := safeRuntime_block_3904_fallthrough
      (by simp [execAllocatedStack, execGuardSaved]; omega) heq h
    have h₂ := safeRuntime_block_3916 (by
      simp [safeRuntime_block_3904_fallthrough_stack, execGuardSaved]; omega) (by jump_dest) h₁
    refine .inr ⟨⟨0⟩, k + 10 + 3, C + 32 + 14, fun he ↦ (hz he).elim, ?_⟩
    simpa only [execCallGas, if_neg hz] using h₂

end Benchmarks.Safe
