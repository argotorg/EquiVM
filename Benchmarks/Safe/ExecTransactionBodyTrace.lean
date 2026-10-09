import Benchmarks.Safe.ExecTransactionPrepare
import Benchmarks.Safe.ExecTransactionGuardTrace
import Benchmarks.Safe.ExecTransactionAfterGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeExecTransactionBodyTrace (evm : EVM.State)
    {I g s0 σ k C aw rdata dataLen sigLen} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨3533⟩
      (execTransactionDecodedStack I.calldata dataLen ⟨128⟩ (⟨759⟩ :: R))
      (memoryBytesDecoded (execTransactionCalldataInput I.calldata dataLen sigLen).signatures)
      aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hb : ExecTransactionCalldataBounds I.calldata dataLen sigLen)
    (ho : (calldataWord I.calldata 100).toNat < 2) (hn : sigLen ≤ 2 ^ 64 - 192)
    (hov : R.length + 70 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecTransitionBody config contract evm
      (execTransactionCalldataInput I.calldata dataLen sigLen).args
      exectransactionTransition.body .reverted) ∨
    (RDstatic safeBytecode g s0 ∧ ExecTransitionBody config contract evm
      (execTransactionCalldataInput I.calldata dataLen sigLen).args
      exectransactionTransition.body .staticViolation) ∨
    ∃ frame' evm' σ' z,
      ExecTransitionBody config contract evm
        (execTransactionCalldataInput I.calldata dataLen sigLen).args
        exectransactionTransition.body (.returned frame' evm' (some [.bool z])) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RDret safeBytecode g s0 σ' z.toUInt256.toByteArray := by
  let p := execTransactionCalldataInput I.calldata dataLen sigLen
  obtain ⟨hr, hs⟩ | ⟨hr, hs⟩ |
      ⟨evm₁, mem₁, ptr₁, out₁, aw₁, k₁, C₁, prefix₁, he₁, hw₁, h₁,
        hsig₁, hf₁, hz₁, hsigEnd, hp₁⟩ :=
    safeExecTransactionPrepare evm h hee hacc hworld hb ho hn (by simp; omega)
  · exact .inl ⟨hr, .execBlockRevert hs⟩
  · exact .inr (.inl ⟨hr, .execBlockStatic hs⟩)
  obtain ⟨hr, hs⟩ |
      ⟨locals, evm₂, mem₂, aw₂, out₂, k₂, C₂, prefix₂, hl₂, hg₂, hh₂, he₂, hw₂,
        h₂, hf₂, hz₂, hm₂⟩ :=
    safeExecTransactionGuard evm evm₁ h₁ he₁ rfl hw₁ hb ho hsig₁ hf₁ hz₁ hsigEnd
      (by omega) (by simp; omega)
  · exact .inl ⟨hr, .execBlockRevert (prefix₁ _ hs)⟩
  have hdata : p.tx.payload.size = dataLen := execTransactionPayloadSize hb
  have hsrc : execTransactionDataStart I.calldata < UInt256.size := by
    have := hb.dataEnd
    have := lt_size_of_lt_sign hb.small
    omega
  obtain ⟨hr, hs⟩ | ⟨hr, hs⟩ | ⟨frame', evm', σ', z, hs, he', ha', hw', hr⟩ :=
    safeExecTransactionAfterGuard p evm₂ h₂ he₂ rfl hw₂ hl₂ hg₂ hh₂ hf₂ hz₂ hm₂
      (by omega) hp₁ hsrc (by rw [hdata]; exact hb.dataEnd)
      (by rw [hdata]; rfl) (by rw [hdata]; have := hb.dataLength; omega) ho (by omega)
  · exact .inl ⟨hr, .execBlockRevert (prefix₁ _ (prefix₂ _ hs))⟩
  · exact .inr (.inl ⟨hr, .execBlockStatic (prefix₁ _ (prefix₂ _ hs))⟩)
  · exact .inr (.inr ⟨frame', evm', σ', z, .execBlockRet (prefix₁ _ (prefix₂ _ hs)),
      he', ha', hw', hr⟩)

end Benchmarks.Safe
