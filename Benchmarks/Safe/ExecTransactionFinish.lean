import Benchmarks.Safe.ExecTransactionEvent
import Benchmarks.Safe.ExecAfterGuardTrace
import Benchmarks.Safe.BoolReturnMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecTransactionFinish (p : ExecTransactionInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata src} {sigPtr guard hash used paid ptr : UInt256}
    {z : Bool} {R : List UInt256} {frame : Frame}
    (h : RD safeBytecode I g s0 ⟨4016⟩
      (paid :: used :: execResultSaved p src sigPtr guard hash z (⟨759⟩ :: R))
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hg : frame.locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)))
    (hh : frame.locals["txHash"]? = some (wordBytes32Value hash))
    (hz : frame.locals["success"]? = some (.bool z))
    (hpaid : frame.locals["payment"]? = some (uint256Value paid))
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 68 < UInt256.size) (hov : R.length + 36 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecBlock config frame evm
      (exectransactionTransition.body.drop 18) .reverted) ∨
    (RDstatic safeBytecode g s0 ∧ ExecBlock config frame evm
      (exectransactionTransition.body.drop 18) .staticViolation) ∨
    ∃ frame' evm' σ',
      ExecBlock config frame evm (exectransactionTransition.body.drop 18)
        (.returned frame' evm' (some [.bool z])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RDret safeBytecode g s0 σ' z.toUInt256.toByteArray := by
  obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeExecEventPrepare p h (by simp; omega)
  cases hperm : I.perm with
  | false =>
    have hr := safeExecEventLogStatic z h₁ (by simp [execResultSaved]; omega) hperm
    exact .inr (.inl ⟨hr, .consStatic
      (safeExecEventSourceStatic hz hh hpaid (by rwa [hee]))⟩)
  | true =>
    obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeExecEventLog z h₁
      (by simp [execResultSaved]; omega) hperm
    rw [hf] at h₂
    have hf₂ : memLoad ⟨64⟩ (writeWord mem ptr.toNat paid) = ptr := by
      rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 by rfl,
        writeWordReadBelow _ _ _ _ _ hm hp]
      exact (memLoadReadWord mem ⟨64⟩).symm.trans hf
    have hm₂ : 96 ≤ (writeWord mem ptr.toNat paid).size := by
      rw [writeWord_sparse_size]; omega
    obtain ⟨hr, hs⟩ | ⟨frame', evm', σ', mem', aw', out, k', C', hs, hz', he', ha', hw',
        h₃, hmem⟩ := safeExecAfterGuardTrace z evm h₂ hee hacc hworld hg hh hz hf₂ hm₂ hp hb
          (by simp [execResultSaved]; omega)
    · exact .inl ⟨hr, .consNormal (safeExecEventSource hz hh hpaid) (.consRevert hs)⟩
    have h₄ := safeRuntime_block_4255 (by simp; omega) (by jump_dest) h₃
    have hf' : memLoad ⟨64⟩ mem' = ptr := by
      rcases hmem with rfl | rfl
      · exact hf₂
      · exact safeExecAfterGuardMemoryFree z hf₂ hm₂ hp
    have hm' : 96 ≤ mem'.size := by
      rcases hmem with rfl | rfl
      · exact hm₂
      · rw [execAfterGuardMemory, selectorWordPairMemory_size]; omega
    have hr := safeReturnBoolFromMemory h₄ (by omega) hf' hm' hp
    have hret : ExecBlock config frame' evm' [.return [.var "success"]]
        (.returned frame' evm' (some [.bool z])) :=
      .consReturn (.return (evalExprs?_singleton (evalLocalValue hz')))
    exact .inr (.inr ⟨frame', evm', σ', .consNormal (safeExecEventSource hz hh hpaid)
      (.consNormal hs hret), he', ha', hw', hr⟩)

end Benchmarks.Safe
