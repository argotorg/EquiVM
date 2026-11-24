import Benchmarks.Safe.ViaIR.ContractSignaturePrepare
import Benchmarks.Safe.ViaIR.ContractSignatureReturn
import Benchmarks.Safe.ViaIR.RawStaticCall
import Benchmarks.Safe.ViaIR.ContractSignatureReject

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

theorem safeContractSignatureTrace (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src} {signature : ByteArray}
    {hash owner last sig : UInt256} {R : List UInt256} (evm : EVM.State)
    (h : RD fork safeBytecode I g s0 ⟨7707⟩
      (UInt256.ofNat src :: last :: owner :: sig :: hash :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hz : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat signature.size)
    (hw : WordArrayMemory mem (src + 32) words)
    (hn : words.length = (signature.size + 31) / 32)
    (hs : (wordBytes words).extract 0 signature.size = signature)
    (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr + 32)
    (hb : contractSignatureCallEnd ptr signature.size + 32 < UInt256.size)
    (hreturn : contractSignatureCallEnd ptr signature.size + 2 ^ 138 + 64 < UInt256.size)
    (hsmall : contractSignatureCallLength signature.size ≤ maxReturnDataSizeByGas)
    (hov : R.length + 23 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ∃ evm' z out,
      callViaEVM fork evm (EVM.address (AccountAddress.ofUInt256 owner)) 0
        (contractSignatureCallBytes hash signature) (z, evm', out) false ∧
      contractSignatureResult z out = false) ∨
    ∃ evm' σ' z out aw' k' C',
      callViaEVM fork evm (EVM.address (AccountAddress.ofUInt256 owner)) 0
        (contractSignatureCallBytes hash signature) (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      contractSignatureResult z out = true ∧
      RD fork safeBytecode I g s0 ⟨7803⟩ (last :: owner :: sig :: hash :: R)
        (signatureReturnMemory (contractSignatureCallMemory mem ptr signature.size hash words)
          (contractSignatureCallEnd ptr signature.size) out) aw' out σ' k' C' ∧
      out.size < 2 ^ 138 ∧
      (if out.size = 0 then contractSignatureCallEnd ptr signature.size else
        contractSignatureCallEnd ptr signature.size + 32 + ABI.paddedSize out.size) < 2 ^ 64 := by
  have hptr : ptr + 32 < UInt256.size := by
    dsimp [contractSignatureCallEnd] at hb
    omega
  have hlen : contractSignatureCallLength signature.size < UInt256.size := by
    dsimp [contractSignatureCallEnd, contractSignatureCallLength] at hb ⊢
    omega
  obtain hrev | ⟨_, _, _, _, hcallSmall, h₁⟩ :=
    safeContractSignaturePrepare words h hf hl hw hn (by omega) hin ha hb hov
  · obtain ⟨z, evm', out, hc, hz⟩ :=
      contractSignatureCanReject evm (AccountAddress.ofUInt256 owner) hash signature
    exact .inl ⟨hrev, evm', z, out, hc, hz⟩
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, hac, hworld', h₂, hout, hbound⟩ :=
    rawStaticCallTraceFrom evm h₁ hee hacc hworld (by native_decide) (by simp; omega)
  rw [callOutputMem_zero] at h₂
  have ho : out.size < 2 ^ 138 := hbound (by
    rw [paddedReadSize, ulit_toNat' _ hlen]
    exact hsmall)
  have hc' : callViaEVM fork evm (EVM.address (AccountAddress.ofUInt256 owner)) 0
      (contractSignatureCallBytes hash signature) (z, evm', out) false := by
    simpa only [addressOfAddress, ulit_toNat' (ptr + 32) hptr,
      ulit_toNat' (contractSignatureCallLength signature.size) hlen,
      contractSignatureCallMemory_read _ _ _ _ _ hn (by omega) hptr hs] using hc
  have hf' := contractSignatureCallMemory_free mem ptr signature.size hash words hn (by omega)
  have hb' : contractSignatureCallEnd ptr signature.size + out.size + 64 < UInt256.size := by
    omega
  obtain hrev | ⟨_, _, _, h₃, hcap⟩ :=
    safeContractSignatureReturnBuffer h₂ hf' hb' (by simp; omega)
  · obtain ⟨z, evm', out, hc, hz⟩ :=
      contractSignatureCanReject evm (AccountAddress.ofUInt256 owner) hash signature
    exact .inl ⟨hrev, evm', z, out, hc, hz⟩
  have hl' : memLoad (signatureReturnDataPtr (contractSignatureCallEnd ptr signature.size) out)
      (signatureReturnMemory (contractSignatureCallMemory mem ptr signature.size hash words)
        (contractSignatureCallEnd ptr signature.size) out) = UInt256.ofNat out.size := by
    by_cases he : out.size = 0
    · simp only [signatureReturnDataPtr, signatureReturnMemory, he, if_true]
      rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
        contractSignatureCallMemory_preserved _ _ _ _ _ _ _ hn hm (by decide) hp,
        ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]
      rfl
    · simp only [signatureReturnDataPtr, signatureReturnMemory, if_neg he]
      apply memLoad_of_wordRead
      rw [ulit_toNat' _ (by omega), returnDataMemory_length]
  have hw' : out.size = 32 →
      memLoad (signatureReturnDataPtr (contractSignatureCallEnd ptr signature.size) out +
        UInt256.ofNat 32)
        (signatureReturnMemory (contractSignatureCallMemory mem ptr signature.size hash words)
          (contractSignatureCallEnd ptr signature.size) out) = calldataWord out 0 := by
    intro he
    have hne : out.size ≠ 0 := by omega
    simp only [signatureReturnDataPtr, signatureReturnMemory, if_neg hne]
    apply memLoad_of_wordRead
    have h32 : (UInt256.ofNat (contractSignatureCallEnd ptr signature.size) +
        UInt256.ofNat 32).toNat = contractSignatureCallEnd ptr signature.size + 32 :=
      uadd_ofNat_toNat (by omega) (by decide) (by omega)
    rw [h32, returnDataMemory_word _ _ _ (by omega)]
  have hfinish := safeContractSignatureFinish h₃ hl' hw' hout (by simp; omega)
  cases hv : contractSignatureResult z out
  · have hr : RDrev fork safeBytecode g s0 := by simpa only [hv, Bool.false_eq_true, if_false]
      using hfinish
    exact .inl ⟨hr, evm', z, out, hc', hv⟩
  · obtain ⟨aw'', k'', C'', h₄⟩ := by simpa only [hv, if_true] using hfinish
    exact .inr ⟨evm', σ', z, out, aw'', k'', C'', hc', he, hac, hworld', hv, h₄, ho,
      hcap hcallSmall⟩

end Benchmarks.Safe.ViaIR
