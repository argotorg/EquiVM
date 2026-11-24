import Benchmarks.Safe.V3_77901a5.ContractSignaturePrepare
import Benchmarks.Safe.V3_77901a5.ContractSignatureReturn
import Benchmarks.Safe.V3_77901a5.RawStaticCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

theorem safeContractSignatureTrace (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src subptr} {signature : ByteArray}
    {hash offset owner ret : UInt256} {R : List UInt256} (evm : EVM.State)
    (h : RD fork safeBytecode I g s0 ⟨7036⟩
      (UInt256.ofNat signature.size :: offset :: UInt256.ofNat src :: hash :: owner :: ret :: R)
      mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr)
    (hsub : UInt256.ofNat 32 + (offset + UInt256.ofNat src) = UInt256.ofNat subptr)
    (hl : memLoad (UInt256.ofNat subptr) mem = UInt256.ofNat signature.size)
    (hw : WordArrayMemory (contractSignatureHeaderMemory mem ptr hash) (subptr + 32) words)
    (hn : words.length = (signature.size + 31) / 32)
    (hs : (wordBytes words).extract 0 signature.size = signature)
    (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr) (hz : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hin : subptr + 32 ≤ mem.size) (ha : subptr + 32 ≤ ptr)
    (hsrc : subptr + 32 + 32 * words.length ≤ ptr + 100)
    (hb : ptr + 512 + 64 * words.length + 2 ^ 139 < UInt256.size)
    (hsmall : contractSignatureCallLength signature.size ≤ maxReturnDataSizeByGas)
    (hov : R.length + 33 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ evm' σ' z out,
      callViaEVM fork evm (EVM.address (AccountAddress.ofUInt256 owner)) 0
        (contractSignatureCallBytes hash signature) (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      out.size < 2 ^ 138 ∧
      ((RDrev fork safeBytecode g s0 ∧ contractSignatureResult z out = false) ∨
        ∃ aw' k' C', RD fork safeBytecode I g s0 ret R
          (signatureReturnMemory (contractSignatureCallMemory mem ptr signature.size hash words)
            (contractSignatureCallEnd ptr signature.size) out) aw' out σ' k' C' ∧ contractSignatureResult z out = true) := by
  have hptr : ptr + 32 < UInt256.size := by omega
  have hcl : contractSignatureCallLength signature.size < UInt256.size := by
    dsimp [contractSignatureCallLength, ABI.paddedSize]
    rw [hn] at hb
    omega
  obtain ⟨_, _, _, _, h₁⟩ := safeContractSignaturePrepare words h hf hsub hl hw hn
    (by omega) (by omega) hin ha hsrc (by omega) hov
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, hac, hworld', h₂, hout, hbound⟩ :=
    rawStaticCallTraceFrom evm h₁ hee hacc hworld (by native_decide) (by simp; omega)
  have ho : out.size < 2 ^ 138 := hbound (by
    rw [paddedReadSize, ulit_toNat' _ hcl]
    exact hsmall)
  have ht : AccountAddress.ofUInt256 (UInt256.land owner solcAddrMask) =
      EVM.address (AccountAddress.ofUInt256 owner) := by
    rw [addressOfAddress]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      (addressOfNat_eq_of_masked_word owner).symm
  have hc' : callViaEVM fork evm (EVM.address (AccountAddress.ofUInt256 owner)) 0
      (contractSignatureCallBytes hash signature) (z, evm', out) false := by
    simpa only [ht, ulit_toNat' (contractSignatureCallEnd ptr signature.size) (by
      dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]; rw [hn] at hb; omega),
      ulit_toNat' (contractSignatureCallLength signature.size) hcl,
      contractSignatureCallMemory_read _ _ _ _ _ hn (by omega) hptr hs] using hc
  refine ⟨evm', σ', z, out, hc', he, hac, hworld', ho, ?_⟩
  rw [callOutputMem_zero] at h₂
  have hf' := contractSignatureCallMemory_free mem ptr signature.size hash words hn
    (by omega) (by omega)
  have hbout : contractSignatureCallEnd ptr signature.size + out.size + 64 < UInt256.size := by
    dsimp [contractSignatureCallEnd, contractSignatureCallLength, ABI.paddedSize]
    rw [hn] at hb
    omega
  have hz' : memLoad ⟨96⟩ (contractSignatureCallMemory mem ptr signature.size hash words) = ⟨0⟩ := by
    rw [memLoadReadWord, show (⟨96⟩ : UInt256).toNat = 96 from rfl,
      contractSignatureCallMemory_preserved _ _ _ _ _ _ _ hn hm (by decide) hp,
      ← show (⟨96⟩ : UInt256).toNat = 96 from rfl, ← memLoadReadWord, hz]
  obtain ⟨_, _, _, h₃⟩ := safeContractSignatureReturnBuffer h₂ hf' hbout (by simp; omega)
  obtain ⟨_, _, _, h₄⟩ := safeContractSignatureFinish h₃
    (signatureReturnMemory_length _ _ _ hz' (by omega))
    (fun hs ↦ signatureReturnMemory_word _ _ _ hs (by omega))
    hout (by simp; omega) (by jump_dest)
  exact safeContractSignatureRequire h₄ (by omega) hret

end Benchmarks.Safe.V3_77901a5
