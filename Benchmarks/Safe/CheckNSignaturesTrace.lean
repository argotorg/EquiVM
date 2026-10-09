import Benchmarks.Safe.SignatureLoop
import Benchmarks.Safe.SignatureBoundsTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeCheckNSignaturesTrace (p : SignatureInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr src} {executor ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨1959⟩
      (p.required :: UInt256.ofNat src :: p.hash :: executor :: ret :: R) mem aw rdata σ k C)
    (he : p.executor = AccountAddress.ofUInt256 executor)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hm : BytesMemory mem src p.signatures) (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hz : memLoad ⟨96⟩ mem = ⟨0⟩) (hsrc : 128 ≤ src)
    (ha : src + 32 + p.signatures.size ≤ ptr) (hp : ptr < 2 ^ 220)
    (hn : p.signatures.size < 2 ^ 64) (hov : R.length + 44 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    (RDrev safeBytecode g s0 ∧
      ExecFuncBody config p.frame evm checkNSignaturesImplFunction.body .reverted) ∨
    ∃ f' evm' σ' mem' ptr' aw' out k' C',
      ExecFuncBody config p.frame evm checkNSignaturesImplFunction.body
        (.returned f' evm' none) ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret R mem' aw' out σ' k' C' ∧
      BytesMemory mem' src p.signatures ∧ memLoad ⟨64⟩ mem' = UInt256.ofNat ptr' ∧
      memLoad ⟨96⟩ mem' = ⟨0⟩ ∧ ptr ≤ ptr' ∧ ptr' ≤ ptr + 2 ^ 204 ∧
      mem'.size ≤ max mem.size (ptr + 2 ^ 204) ∧ MemoryPreserves mem mem' 96 ptr := by
  have hn' : p.signatures.size < UInt256.size := lt_trans hn (by decide)
  obtain ⟨hrev, hbody⟩ | ⟨aw₁, k₁, C₁, hreq, h₁⟩ :=
    safeSignatureBoundsTrace p evm h hm hn' (by omega)
  · exact .inl ⟨hrev, hbody⟩
  have hcount : p.required.toNat < 2 ^ 64 := by
    dsimp [SignatureInput.requiredBytes] at hreq
    omega
  have hbudget : ptr + p.required.toNat * 2 ^ 140 < 2 ^ 224 := by omega
  have hcurrent : p.loopFrame.locals["currentOwner"]? =
      some (.address (AccountAddress.ofNat 0)) := by
    simp [SignatureInput.loopFrame, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  obtain ⟨hrev, hbody⟩ | ⟨f', evm', σ', mem', ptr', aw', out, k', C', hbody, hee', hacc', hw',
      h₂, hm', hf', hz', hpl, hph, hms, hpres⟩ :=
    safeSignatureLoop p.required.toNat p evm (i := 0) h₁ (SignatureContext.initial p)
      he hcurrent hee hacc hworld hm hf hz hsrc ha hbudget hn hreq (by simp) hov hret
  · exact .inl ⟨hrev, safeSignatureSourcePrefix p evm hn' hreq (execBlock_singleton hbody)⟩
  exact .inr ⟨f', evm', σ', mem', ptr', aw', out, k', C',
    safeSignatureSourcePrefix p evm hn' hreq (execBlock_singleton hbody), hee', hacc', hw',
    h₂, hm', hf', hz', hpl, by omega, by omega, hpres⟩

end Benchmarks.Safe
