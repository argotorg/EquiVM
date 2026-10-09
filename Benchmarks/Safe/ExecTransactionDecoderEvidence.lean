import Benchmarks.Safe.ExecTransactionDecoder
import Benchmarks.Safe.ExecTransactionDecodeReverts
import Benchmarks.Safe.MemoryBytesDecodeEvidence

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeDecodeExecTransactionEvidence {I g s0 σ k C aw rdata}
    {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9917⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 28 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨ ∃ dataLen sigLen aw' k' C',
      ExecTransactionCalldataBounds I.calldata dataLen sigLen ∧
      (calldataWord I.calldata 100).toNat < 2 ∧ sigLen ≤ 2 ^ 64 - 192 ∧
      RD safeBytecode I g s0 ret (execTransactionDecodedStack I.calldata dataLen ⟨128⟩ R)
        (memoryBytesDecoded (execTransactionCalldataInput I.calldata dataLen sigLen).signatures)
        aw' rdata σ k' C' := by
  by_cases hh : 324 ≤ I.calldata.size
  swap
  · exact .inl (safeExecDecodeHeadRevert h
      (solcDecodeLenCheckShort hlong (by change I.calldata.size < 324; omega) hsize (by decide))
      hov)
  by_cases hhi : I.calldata.size < 2 ^ 255 + 4
  swap
  · exact .inl (safeExecDecodeHeadRevert h
      (solcDecodeLenCheckHuge (by change 2 ^ 255 + 4 ≤ I.calldata.size; omega)
        hsize (by decide)) hov)
  obtain ⟨_, _, h₁⟩ := safeExecDecodeTargetStart h
    (solcDecodeLenCheckOk hh (by change I.calldata.size < 2 ^ 255 + 4; exact hhi)
      hsize (by decide)) (by omega)
  by_cases ht : (calldataWord I.calldata 4).toNat < EVM.addressModulus
  swap
  · exact .inl (safeReadCalldataAddressRevert h₁ ht (by simp [execDecodeTargetSaved]; omega))
  obtain ⟨_, _, h₂⟩ := safeReadCalldataAddress h₁ ht
    (by simp [execDecodeTargetSaved]; omega) (by jump_dest)
  by_cases hdo : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1
  swap
  · exact .inl (safeExecDecodeDataOffsetRevert h₂ hdo hov)
  obtain ⟨_, _, h₃⟩ := safeExecDecodeDataStart h₂ hdo (by omega)
  obtain hr | ⟨dataLen, _, _, hdw, hdn, hs, hdi, h₄⟩ :=
    safeDecodeCalldataBytesEvidence h₃ (by omega) hsize
      (by simp [execDecodeDataSaved]; omega) (by jump_dest)
  · exact .inl hr
  obtain ⟨_, _, h₅⟩ := safeExecDecodeOperationStart h₄ (by omega)
  by_cases ho : (calldataWord I.calldata 100).toNat < 2
  swap
  · exact .inl (safeDecodeOperationRevert h₅ ho (by simp [execDecodeOperationSaved]; omega))
  obtain ⟨_, _, h₆⟩ := safeDecodeOperation h₅ ho
    (by simp [execDecodeOperationSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₇⟩ := safeExecDecodeTokenStart h₆ (by omega)
  by_cases hk : (calldataWord I.calldata 228).toNat < EVM.addressModulus
  swap
  · exact .inl (safeReadCalldataAddressRevert h₇ hk (by simp [execDecodeTokenSaved]; omega))
  obtain ⟨_, _, h₈⟩ := safeReadCalldataAddress h₇ hk
    (by simp [execDecodeTokenSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₉⟩ := safeExecDecodeReceiverStart h₈ (by omega)
  by_cases hr : (calldataWord I.calldata 260).toNat < EVM.addressModulus
  swap
  · exact .inl (safeReadCalldataAddressRevert h₉ hr (by simp [execDecodeReceiverSaved]; omega))
  obtain ⟨_, _, h₁₀⟩ := safeReadCalldataAddress h₉ hr
    (by simp [execDecodeReceiverSaved]; omega) (by jump_dest)
  by_cases hso : (calldataWord I.calldata 292).toNat ≤ 2 ^ 64 - 1
  swap
  · exact .inl (safeExecDecodeSignaturesOffsetRevert h₁₀ hso hov)
  obtain ⟨_, _, h₁₁⟩ := safeExecDecodeSignaturesStart h₁₀ hso (by omega)
  obtain hrev | ⟨sigLen, aw', _, _, hsw, hsn, _, hsi, h₁₂⟩ :=
    safeDecodeMemoryBytesEvidence h₁₁ (by omega) hsize
      (by simp [execDecodeSignaturesSaved]; omega) (by jump_dest)
  · exact .inl hrev
  obtain ⟨k', C', h₁₃⟩ := safeExecDecodeFinish h₁₂ (by omega) hret
  exact .inr ⟨dataLen, sigLen, aw', k', C',
    ⟨hh, hs, ht, hdo, hdw, hdn, hdi, by omega, hk, hr, hso, hsw, by omega, hsi⟩,
    ho, hsn, h₁₃⟩

end Benchmarks.Safe
