import Benchmarks.Safe.ContractSignaturePrepare
import Benchmarks.Safe.ContractSignatureReturn
import Benchmarks.Safe.RawStaticCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeContractSignatureTrace (words : List UInt256)
    {I g s0 σ k C aw mem rdata ptr src} {signature : ByteArray}
    {hash owner ret : UInt256} {R : List UInt256} (evm : EVM.State)
    (h : RD safeBytecode I g s0 ⟨8677⟩
      (UInt256.ofNat src :: hash :: owner :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ) (hworld : evm.σ₀ = s0.σ₀)
    (hf : memLoad ⟨64⟩ mem = UInt256.ofNat ptr) (hz : memLoad ⟨96⟩ mem = ⟨0⟩)
    (hl : memLoad (UInt256.ofNat src) mem = UInt256.ofNat signature.size)
    (hw : WordArrayMemory mem (src + 32) words)
    (hn : words.length = (signature.size + 31) / 32)
    (hs : (wordBytes words).extract 0 signature.size = signature)
    (hm : 128 ≤ mem.size) (hp : 128 ≤ ptr)
    (hin : src + 32 + 32 * words.length ≤ mem.size)
    (ha : src + 32 + 32 * words.length ≤ ptr + 36)
    (hb : contractSignatureCallEnd ptr signature.size +
      contractSignatureCallLength signature.size + 64 < UInt256.size)
    (hreturn : contractSignatureCallEnd ptr signature.size + 2 ^ 138 + 64 < UInt256.size)
    (hsmall : contractSignatureCallLength signature.size ≤ maxReturnDataSizeByGas)
    (hov : R.length + 26 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ evm' σ' z out aw' k' C',
      callViaEVM evm (EVM.address (AccountAddress.ofUInt256 owner)) 0
        (contractSignatureCallBytes hash signature) (z, evm', out) false ∧
      evm'.executionEnv = I ∧ evm'.accountMap = σ' ∧ evm'.σ₀ = s0.σ₀ ∧
      RD safeBytecode I g s0 ret
        ((if contractSignatureResult z out then ⟨1⟩ else ⟨0⟩) :: R)
        (signatureReturnMemory (contractSignatureCallMemory mem ptr signature.size hash words)
          (contractSignatureCallEnd ptr signature.size) out) aw' out σ' k' C' ∧
      out.size < 2 ^ 138 := by
  have hptr : ptr + 32 < UInt256.size := by
    dsimp [contractSignatureCallEnd] at hb
    omega
  obtain ⟨_, _, _, _, h₁⟩ := safeContractSignaturePrepare words h hf hl hw hn
    (by omega) (by omega) hin ha hb hov
  obtain ⟨evm', σ', z, out, aw', k', C', hc, he, hac, hworld', h₂, hout, hbound⟩ :=
    rawStaticCallTraceFrom evm h₁ hee hacc hworld (by native_decide) (by simp; omega)
  rw [callOutputMem_zero] at h₂
  have ho : out.size < 2 ^ 138 := hbound (by
    rw [paddedReadSize, ulit_toNat' _ (by omega)]
    exact hsmall)
  have ht : AccountAddress.ofUInt256 (UInt256.land solcAddrMask owner) =
      EVM.address (AccountAddress.ofUInt256 owner) := by
    rw [u256_land_comm, addressOfAddress]
    simpa only [accountAddress_ofUInt256_eq_ofNat_toNat] using
      (addressOfNat_eq_of_masked_word owner).symm
  have hc' : callViaEVM evm (EVM.address (AccountAddress.ofUInt256 owner)) 0
      (contractSignatureCallBytes hash signature) (z, evm', out) false := by
    simpa only [ht, ulit_toNat' (contractSignatureCallEnd ptr signature.size) (by omega),
      ulit_toNat' (contractSignatureCallLength signature.size) (by omega),
      contractSignatureCallMemory_read _ _ _ _ _ hn (by omega) hptr hs] using hc
  have hf' := contractSignatureCallMemory_free mem ptr signature.size hash words hn (by omega)
  have hb' : contractSignatureCallEnd ptr signature.size + out.size + 64 < UInt256.size := by
    omega
  obtain ⟨_, _, _, h₃⟩ := safeContractSignatureReturnBuffer h₂ hf' hb' (by simp; omega)
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
  obtain ⟨aw'', k'', C'', h₄⟩ := safeContractSignatureFinish h₃ hl' hw' hout
    (by omega) hret
  exact ⟨evm', σ', z, out, aw'', k'', C'', hc', he, hac, hworld', h₄, ho⟩

end Benchmarks.Safe
