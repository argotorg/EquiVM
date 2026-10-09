import Benchmarks.Safe.CodePrefixMemory
import Benchmarks.Safe.ExternalCode
import Benchmarks.Safe.Blocks.Runtime_039

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

def thisCode (σ : AccountMap) (I : ExecutionEnv) : ByteArray :=
  externalCode σ (UInt256.ofNat I.codeOwner.val)

def delegatedAccount (σ : AccountMap) (I : ExecutionEnv) : Prop :=
  codePrefix3 (thisCode σ I) = ⟨#[0xef, 0x01, 0x00]⟩

instance (σ : AccountMap) (I : ExecutionEnv) : Decidable (delegatedAccount σ I) :=
  inferInstanceAs (Decidable (codePrefix3 (thisCode σ I) = ⟨#[0xef, 0x01, 0x00]⟩))

theorem safeEvalDelegatedAccount (evm : EVM.State) (frame : Frame) :
    evalExpr? config frame evm isThisDelegatedAccountExpr =
      .ok (.bool (decide (delegatedAccount evm.accountMap evm.executionEnv))) := by
  simp [isThisDelegatedAccountExpr, eqE, this, evalExpr?, envValue, evalBinaryOp?,
    EvalResult.bind, EvalResult.ofOption, bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.bytes.injEq, decide_eq_true_eq]
  simp only [delegatedAccount, thisCode, externalCode, accountAddress_roundtrip,
    codePrefix3, ByteArray.size_extract, Nat.sub_zero]
  rfl

theorem safeDelegatedAccountTrace {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9055⟩ (ret :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hmem : 32 ≤ mem.size)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      ((decide (delegatedAccount σ I)).toUInt256 :: R)
      ((thisCode σ I).write 0 mem 0 3) aw' rdata σ k' C' := by
  have hcopy := safeRuntime_block_9055 (by simp; omega) h
  obtain ⟨k₁, C₁, hcopied⟩ := rdExtcodecopy hcopy (by native_decide) (by simp; omega)
  obtain ⟨aw', k', C', hdone⟩ := safeRuntime_block_9063_packed (by omega) hret hcopied
  simp only [safeRuntime_block_9063_stack] at hdone
  change RD safeBytecode I g s0 ret
    (UInt256.eq (UInt256.ofNat 15663360)
      (UInt256.shiftRight (memLoad ⟨0⟩ ((thisCode σ I).write 0 mem 0 3))
        (UInt256.ofNat 232)) :: R)
    ((thisCode σ I).write 0 mem 0 3) aw' rdata σ k' C' at hdone
  rw [copiedPrefix3Check _ _ hmem] at hdone
  exact ⟨aw', k', C', hdone⟩

end Benchmarks.Safe
