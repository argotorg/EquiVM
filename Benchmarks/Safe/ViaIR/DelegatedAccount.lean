import Benchmarks.Safe.ViaIR.CodePrefixMemory
import Benchmarks.Safe.ViaIR.ExternalCode
import Benchmarks.Safe.ViaIR.Blocks.Runtime_049

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

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

set_option maxRecDepth 100000 in
theorem safeDelegatedAccountTrace {I g s0 σ k C aw mem rdata} {flag : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10956⟩ (flag :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hmem : 32 ≤ mem.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨10950⟩
      (UInt256.isZero (decide (delegatedAccount σ I)).toUInt256 :: R)
      ((thisCode σ I).write 0 mem 0 3) aw' rdata σ k' C' := by
  have hcopy := safeRuntime_block_10956 (by omega) h
  obtain ⟨k₁, C₁, hcopied⟩ := rdExtcodecopy hcopy (by native_decide) (by omega)
  obtain ⟨aw', k', C', hdone⟩ := safeRuntime_block_10964_packed (by omega) (by jump_dest) hcopied
  simp only [safeRuntime_block_10964_stack] at hdone
  change RD fork safeBytecode I g s0 ⟨10950⟩
    (UInt256.isZero (UInt256.eq
      (UInt256.shiftRight (memLoad ⟨0⟩ ((thisCode σ I).write 0 mem 0 3))
        (UInt256.ofNat 232)) (UInt256.ofNat 15663360)) :: R)
    ((thisCode σ I).write 0 mem 0 3) aw' rdata σ k' C' at hdone
  rw [uInt256_eq_comm, copiedPrefix3Check _ _ hmem] at hdone
  exact ⟨aw', k', C', hdone⟩

end Benchmarks.Safe.ViaIR
