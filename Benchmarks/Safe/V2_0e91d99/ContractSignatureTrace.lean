import Benchmarks.Safe.V2_0e91d99.ContractSignaturePrepare
import Benchmarks.Safe.V2_0e91d99.ContractSignatureReturn
import Benchmarks.Safe.V2_0e91d99.RawStaticCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99

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
    (hm : 96 ≤ mem.size) (hp : 96 ≤ ptr)
    (hin : subptr + 32 ≤ mem.size) (ha : subptr + 32 ≤ ptr)
    (hsrc : subptr + 32 + 32 * words.length ≤ ptr + 68)
    (hb : ptr + 132 + 32 * words.length < UInt256.size)
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
            ptr out) aw' out σ' k' C' ∧ contractSignatureResult z out = true) := by
  have hptr : ptr + 32 < UInt256.size := by omega
  have hcl : contractSignatureCallLength signature.size < UInt256.size := by
    dsimp [contractSignatureCallLength, ABI.paddedSize]
    rw [hn] at hb
    omega
  obtain ⟨_, _, _, _, h₁⟩ := safeContractSignaturePrepare words h hf hsub hl hw hn
    hm hp hin ha hsrc hb hov
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
    simpa only [ht, ulit_toNat' ptr (by omega),
      ulit_toNat' (contractSignatureCallLength signature.size) hcl,
      contractSignatureCallMemory_read _ _ _ _ _ hn hp hptr hs] using hc
  refine ⟨evm', σ', z, out, hc', he, hac, hworld', ho, ?_⟩
  have hcopy : (min (⟨32⟩ : UInt256) (UInt256.ofNat out.size)).toNat = min 32 out.size :=
    callOutputLength hout
  rw [callOutputMem, hcopy] at h₂
  cases z with
  | false =>
      exact Or.inl ⟨safeContractSignatureCallFailure h₂ (by simp; omega), rfl⟩
  | true =>
      have hf' := contractSignatureArgs_free (len := signature.size) (hash := hash)
        (words := words) hf hm hp hn
      rcases safeContractSignatureReturnBuffer h₂ hf'
        (by rw [contractSignatureCallMemory_size _ _ _ _ _ hn]; omega) hp (by omega)
        (by omega) (by simp; omega) with ⟨hr, hd⟩ | ⟨aw'', k'', C'', h₃, hd⟩
      · exact Or.inl ⟨hr, contractSignatureResult_of_not_decoded hd⟩
      · exact safeContractSignatureFinish h₃ hd (by omega) hret

end Benchmarks.Safe.V2_0e91d99
