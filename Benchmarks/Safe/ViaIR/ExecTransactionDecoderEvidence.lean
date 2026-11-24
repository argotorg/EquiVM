import Benchmarks.Safe.ViaIR.ExecTransactionDecoder
import Benchmarks.Safe.ViaIR.ExecTransactionDecodeReverts
import Benchmarks.Safe.ViaIR.MemoryBytesDecodeEvidence

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeDecodeExecTransactionEvidence {I g s0 σ k C aw rdata}
    {scratch : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4354⟩ (scratch :: R) solcFreePtrMem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 28 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨ ∃ dataLen sigLen aw' k' C',
      ExecTransactionCalldataBounds I.calldata dataLen sigLen ∧
      (calldataWord I.calldata 100).toNat < 2 ∧ sigLen ≤ 2 ^ 64 - 192 ∧
      RD fork safeBytecode I g s0 ⟨4469⟩ (execTransactionDecodedStack I.calldata dataLen ⟨128⟩ R)
        (memoryBytesDecoded (execTransactionCalldataInput I.calldata dataLen sigLen).signatures)
        aw' rdata σ k' C' := by
  by_cases hh : 324 ≤ I.calldata.size
  swap
  · exact .inl (safeExecDecodeHeadRevert h
      (solcDecodeLenCheckShort hlong (by change I.calldata.size < 324; omega) hsize (by decide))
      hlong hsize hov)
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact .inl (safeExecDecodeHeadRevert h
      (solcDecodeLenCheckHuge (by change 2 ^ 255 + 4 ≤ I.calldata.size; omega)
        hsize (by decide)) hlong hsize hov)
  obtain ⟨_, _, h₁⟩ := safeExecDecodeTargetStart h
    (solcDecodeLenCheckOk hh (by change I.calldata.size < 2 ^ 255 + 4; exact hhi)
      hsize (by decide)) hlong hsize (by omega)
  by_cases ht : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · exact .inl (safeDecodeAddressNoncanon h₁ (by simp; omega) ht)
  obtain ⟨_, _, h₂⟩ := safeDecodeAddress h₁ (by simp; omega) ht (by jump_dest)
  by_cases hdo : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1
  swap
  · exact .inl (safeExecDecodeDataOffsetRevert h₂ hdo hov)
  obtain ⟨_, _, h₃⟩ := safeExecDecodeDataStart h₂ hdo (by omega)
  obtain hr | ⟨dataLen, _, _, hdw, hdn, hs, hdi, h₄⟩ :=
    safeDecodeCalldataBytesEvidence h₃ (by omega) hsize
      (by simp [execDecodeDataSaved]; omega) (by jump_dest)
  · exact .inl hr
  by_cases ho : (calldataWord I.calldata 100).toNat < 2
  swap
  · exact .inl (safeExecDecodeOperationRevert h₄ ho hov)
  obtain ⟨_, _, h₅⟩ := safeExecDecodeOperationStart h₄ ho (by omega)
  obtain ⟨_, _, h₆⟩ := safeExecDecodeTokenStart h₅ (by omega)
  by_cases hk : (calldataWord I.calldata 228).toNat < EVM.addressModulus
  swap
  · exact .inl (safeExecDecodeTokenRevert h₆ hk hov)
  obtain ⟨_, _, h₇⟩ := safeExecDecodeReceiverStart h₆ hk (by omega)
  by_cases hr : (calldataWord I.calldata 260).toNat < EVM.addressModulus
  swap
  · exact .inl (safeExecDecodeReceiverRevert h₇ hr hov)
  obtain ⟨_, _, h₁₀⟩ := safeExecDecodeReceiverFinish h₇ hr (by omega)
  by_cases hso : (calldataWord I.calldata 292).toNat ≤ 2 ^ 64 - 1
  swap
  · exact .inl (safeExecDecodeSignaturesOffsetRevert h₁₀ hso hov)
  obtain ⟨_, _, h₁₁⟩ := safeExecDecodeSignaturesStart h₁₀ hso (by omega)
  obtain hrev | ⟨sigLen, aw', k', C', hsw, hsn, _, hsi, h₁₂⟩ :=
    safeDecodeMemoryBytesEvidence h₁₁ (by omega) hsize
      (by simp [execDecodeSignaturesSaved, execDecodeReceiverSaved]; omega) (by jump_dest)
  · exact .inl hrev
  exact .inr ⟨dataLen, sigLen, aw', k', C',
    ⟨hh, hs, ht, hdo, hdw, hdn, hdi, by omega, hk, hr, hso, hsw, by omega, hsi⟩,
    ho, hsn, h₁₂⟩

end Benchmarks.Safe.ViaIR
