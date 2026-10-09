import Benchmarks.Safe.CheckSignaturesSource
import Benchmarks.Safe.CheckNSignaturesTrace
import Benchmarks.Safe.Blocks.Runtime_028
import Benchmarks.Safe.Blocks.Runtime_022
import Benchmarks.Safe.Blocks.Runtime_030

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeCheckSignaturesTrace (p : SignatureCheckInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {executor ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6526⟩
      (UInt256.ofNat src :: p.hash :: executor :: ret :: R) mem aw rdata σ k C)
    (he : p.executor = AccountAddress.ofUInt256 executor)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 220)
    (hn : p.signatures.size < 2 ^ 64) (hov : R.length + 49 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config p.frame evm checkSignaturesImplFunction.body .reverted) ∨
    ∃ f' evm' σ' mem' ptr' aw' out k' C',
      ExecFuncBody config p.frame evm checkSignaturesImplFunction.body (.returned f' evm' none) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret R mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 204 ∧
      mem'.size ≤ max mem.size (ptr + 2 ^ 204) ∧ MemoryPreserves mem mem' 96 ptr := by
  have hload : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (UInt256.ofNat 4) ⟨0⟩)) = storedThreshold evm := by
    simp only [storedThreshold, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, hee, hacc]
    rfl
  by_cases ht : storedThreshold evm = ⟨0⟩
  · obtain ⟨k₁, C₁, h₁⟩ := safeRuntime_block_6526_fallthrough (by simp; omega)
      (by rw [hload, ht]; decide) h
    have h₂ := safeRuntime_block_6538 (by
      simp only [safeRuntime_block_6526_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₁
    exact .inl ⟨safeRuntime_block_6898 (by
      simp only [safeRuntime_block_6538_stack, safeRuntime_block_6526_fallthrough_stack,
        List.length_cons]; omega) h₂, signatureCheckZero p evm ht⟩
  obtain ⟨k₁, C₁, h₁⟩ := safeRuntime_block_6526_taken (by simp; omega)
    (by rw [hload]; exact u256_zero_sub_ne_zero ht) (by jump_dest) h
  simp only [safeRuntime_block_6526_taken_stack, hload] at h₁
  have h₂ := safeRuntime_block_6554 (by simp; omega) (by jump_dest) h₁
  obtain ⟨hrev, hbody⟩ | ⟨f', evm', σ', mem', ptr', aw', out, k', C', hbody, hee', hacc', hw',
      h₃, hm', hf', hz', hpl, hph, hms, hpres⟩ :=
    safeCheckNSignaturesTrace (p.withRequired (storedThreshold evm)) evm h₂ he hee hacc hworld
      hm hf hz hsrc ha hp hn (by simp; omega) (by jump_dest)
  · exact .inl ⟨hrev, .execBlockRevert (signatureCheckSource p evm ht hbody)⟩
  obtain ⟨aw'', k'', C'', h₄⟩ := safeRuntime_block_4283_packed (by omega) hret h₃
  exact .inr ⟨_, evm', σ', mem', ptr', aw'', out, k'', C'',
    .execBlockOK (signatureCheckSource p evm ht hbody), hee', hacc', hw',
    h₄, hm', hf', hz', hpl, hph, hms, hpres⟩

end Benchmarks.Safe
