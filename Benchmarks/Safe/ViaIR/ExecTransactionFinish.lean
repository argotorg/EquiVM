import Benchmarks.Safe.ViaIR.ExecTransactionEvent
import Benchmarks.Safe.ViaIR.ExecAfterGuardTrace
import Benchmarks.Safe.ViaIR.BoolReturnMemory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 5000 in
theorem safeExecTransactionFinish (evm : EVM.State)
    {I g s0 σ k C aw mem rdata} {guard hash paid ptr : UInt256}
    {z : Bool} {R : List UInt256} {frame : Frame}
    (h : RD fork safeBytecode I g s0 ⟨4763⟩ (execEventSaved guard hash paid z R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hg : frame.locals["guard"]? = some (.address (AccountAddress.ofUInt256 guard)))
    (hh : frame.locals["txHash"]? = some (wordBytes32Value hash))
    (hz : frame.locals["success"]? = some (.bool z))
    (hpaid : frame.locals["payment"]? = some (uint256Value paid))
    (hf : memLoad ⟨64⟩ mem = ptr) (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr.toNat)
    (hb : ptr.toNat + 68 < UInt256.size) (hcap : ptr.toNat < 2 ^ 64)
    (hov : R.length + 36 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecBlock fork config frame evm
      (exectransactionTransition.body.drop 18) .reverted) ∨
    (RDstatic fork safeBytecode g s0 ∧ ExecBlock fork config frame evm
      (exectransactionTransition.body.drop 18) .staticViolation) ∨
    ∃ frame' evm' σ',
      ExecBlock fork config frame evm (exectransactionTransition.body.drop 18)
        (.returned frame' evm' (some [.bool z])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RDret fork safeBytecode g s0 σ' z.toUInt256.toByteArray := by
  obtain ⟨k₁, C₁, h₁⟩ := safeExecEventPrepare h (by omega)
  simp only [execEventSaved, List.cons_append, List.nil_append] at h₁
  cases hperm : I.perm with
  | false =>
    have hr := safeExecEventLogStatic z h₁ (by simp; omega) hperm
    exact .inr (.inl ⟨hr, .consStatic
      (safeExecEventSourceStatic hz hh hpaid (by rwa [hee]))⟩)
  | true =>
    obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeExecEventLog z h₁
      (by simp; omega) hperm
    rw [hf] at h₂
    have hf₂ : memLoad ⟨64⟩ (writeWord mem ptr.toNat paid) = ptr := by
      rw [memLoadReadWord, show (⟨64⟩ : UInt256).toNat = 64 by rfl,
        writeWordReadBelow _ _ _ _ _ hm hp]
      exact (memLoadReadWord mem ⟨64⟩).symm.trans hf
    obtain ⟨hr, hs⟩ | ⟨frame', evm', σ', mem', aw', out, a, b, c, k', C', hs, hz',
        he', ha', hw', h₃⟩ := safeExecAfterGuardTrace z evm h₂ hee hacc hworld hg hh hz hf₂
          hb hcap (by omega)
    · exact .inl ⟨hr, .consNormal (safeExecEventSource (fork := fork) (hperm := by simpa only [hee] using hperm) hz hh hpaid) (.consRevert hs)⟩
    have hr := safeReturnBoolFromMemory h₃ (by simp; omega)
    have hret : ExecBlock fork config frame' evm' [.return [.var "success"]]
        (.returned frame' evm' (some [.bool z])) :=
      .consReturn (.return (evalExprs?_singleton (evalLocalValue hz')))
    exact .inr (.inr ⟨frame', evm', σ', .consNormal (safeExecEventSource (fork := fork) (hperm := by simpa only [hee] using hperm) hz hh hpaid)
      (.consNormal hs hret), he', ha', hw', hr⟩)

end Benchmarks.Safe.ViaIR
