import Benchmarks.Safe.V2_0e91d99.DelegationMemory
import Benchmarks.Safe.V2_0e91d99.ExternalCode
import Benchmarks.Safe.V2_0e91d99.ByteCopy
import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_038

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

namespace Benchmarks.Safe.V2_0e91d99

set_option maxRecDepth 1000

def delegatedAccount (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  delegationPrefix (externalCode σ (UInt256.ofNat I.codeOwner.val)) = ⟨#[0xef, 0x01, 0x00]⟩

instance (σ : AccountMap) (I : ExecutionEnv) : Decidable (delegatedAccount σ I) :=
  inferInstanceAs (Decidable (_ = _))

theorem safeEvalDelegatedAccount (evm : EVM.State) (frame : Frame) :
    evalExpr? config frame evm delegatedThisExpr =
      .ok (.bool (decide (delegatedAccount evm.accountMap evm.executionEnv))) := by
  simp [delegatedThisExpr, eqE, this, evalExpr?, envValue, externalCode,
    AccountAddress.ofUInt256_ofNat, State.lookupAccount, delegationPrefix, delegatedAccount,
    evalBinaryOp?, EvalResult.bind, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.bytes.injEq, decide_eq_true_eq]

theorem safeDelegatedAccountTrace {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8928⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hm : 32 ≤ mem.size)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ret
      ((if delegatedAccount σ I then ⟨1⟩ else ⟨0⟩) :: R)
      ((externalCode σ (UInt256.ofNat I.codeOwner.val)).write 0 mem 0 3)
      aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_8928 (by simp; omega) h
  simp only [safeRuntime_block_8928_stack] at h₁
  obtain ⟨k₂, C₂, h₂⟩ := rdExtcodecopy h₁ (by native_decide) (by simp; omega)
  change RD fork safeBytecode I g s0 ⟨8936⟩ (⟨0⟩ :: ret :: R)
    ((externalCode σ (UInt256.ofNat I.codeOwner.val)).write 0 mem 0 3)
    (M aw ⟨0⟩ ⟨3⟩) rdata σ k₂ C₂ at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_8936_packed (by simp; omega) hret h₂
  simp only [safeRuntime_block_8936_stack] at h₃
  change RD fork safeBytecode I g s0 ret
    ((UInt256.eq ⟨15663360⟩ (UInt256.shiftRight
      (memLoad ⟨0⟩ ((externalCode σ (UInt256.ofNat I.codeOwner.val)).write 0 mem 0 3))
      ⟨232⟩)) :: R) _ aw₃ rdata σ k₃ C₃ at h₃
  rw [delegationWord _ _ hm] at h₃
  exact ⟨aw₃, k₃, C₃, h₃⟩

end Benchmarks.Safe.V2_0e91d99
