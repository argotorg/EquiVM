import Benchmarks.Safe.SetupDecodeScalars
import Benchmarks.Safe.SetupDecodeOwnersEvidence
import Benchmarks.Safe.CalldataBytesDecoder

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeDecodeSetupValid {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10399⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hov : R.length + 24 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, h₁⟩ := safeSetupDecodeOwnersValid h hb.head hb.small hb.ownersOffset
    hb.ownersWord hb.ownersLength hb.ownersEnd (by omega)
  obtain ⟨_, _, h₂⟩ := safeSetupDecodeTargetStart h₁ hb.ownersOffset (by omega)
  obtain ⟨_, _, h₃⟩ := safeReadCalldataAddress h₂ hb.target
    (by simp [setupDecodeTargetSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₄⟩ := safeSetupDecodeDataStart h₃ hb.dataOffset (by omega)
  obtain ⟨_, _, h₅⟩ := safeDecodeCalldataBytesValid h₄ hb.dataWord hb.dataEnd
    hb.small hb.dataLength (by simp [setupDecodeDataSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₆⟩ := safeSetupDecodeFallbackStart h₅ (by omega)
  obtain ⟨_, _, h₇⟩ := safeReadCalldataAddress h₆ hb.fallbackHandler
    (by simp [setupDecodeFallbackSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₈⟩ := safeSetupDecodeTokenStart h₇ (by omega)
  obtain ⟨_, _, h₉⟩ := safeReadCalldataAddress h₈ hb.paymentToken
    (by simp [setupDecodeTokenSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₁₀⟩ := safeSetupDecodeReceiverStart h₉ (by omega)
  obtain ⟨_, _, h₁₁⟩ := safeReadCalldataAddress h₁₀ hb.paymentReceiver
    (by simp [setupDecodeReceiverSaved]; omega) (by jump_dest)
  exact safeSetupDecodeFinish h₁₁ (by omega) hret

set_option maxRecDepth 100000 in
theorem safeDecodeSetupEvidence {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10399⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    RDrev safeBytecode g s0 ∨ ∃ n len k' C', SetupCalldataBounds I.calldata n len ∧
      RD safeBytecode I g s0 ret (setupDecodedStack I.calldata n len R)
        mem aw rdata σ k' C' := by
  obtain hr | ⟨n, _, _, hh, hs, ho, hw, hn, hin, h₁⟩ :=
    safeSetupDecodeOwnersEvidence h hlong hsize (by omega)
  · exact Or.inl hr
  obtain ⟨_, _, h₂⟩ := safeSetupDecodeTargetStart h₁ ho (by omega)
  by_cases ht : (calldataWord I.calldata 68).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeReadCalldataAddressRevert h₂ ht (by simp [setupDecodeTargetSaved]; omega))
  obtain ⟨_, _, h₃⟩ := safeReadCalldataAddress h₂ ht
    (by simp [setupDecodeTargetSaved]; omega) (by jump_dest)
  by_cases hdo : (calldataWord I.calldata 100).toNat ≤ 2 ^ 64 - 1
  swap
  · exact Or.inl (safeSetupDecodeDataOffsetRevert h₃ hdo (by omega))
  obtain ⟨_, _, h₄⟩ := safeSetupDecodeDataStart h₃ hdo (by omega)
  obtain hr | ⟨len, _, _, hlw, hlen, _, hli, h₅⟩ :=
    safeDecodeCalldataBytesEvidence h₄ (by omega) hsize
      (by simp [setupDecodeDataSaved]; omega) (by jump_dest)
  · exact Or.inl hr
  obtain ⟨_, _, h₆⟩ := safeSetupDecodeFallbackStart h₅ (by omega)
  by_cases hf : (calldataWord I.calldata 132).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeReadCalldataAddressRevert h₆ hf
      (by simp [setupDecodeFallbackSaved]; omega))
  obtain ⟨_, _, h₇⟩ := safeReadCalldataAddress h₆ hf
    (by simp [setupDecodeFallbackSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₈⟩ := safeSetupDecodeTokenStart h₇ (by omega)
  by_cases hk : (calldataWord I.calldata 164).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeReadCalldataAddressRevert h₈ hk
      (by simp [setupDecodeTokenSaved]; omega))
  obtain ⟨_, _, h₉⟩ := safeReadCalldataAddress h₈ hk
    (by simp [setupDecodeTokenSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₁₀⟩ := safeSetupDecodeReceiverStart h₉ (by omega)
  by_cases hr : (calldataWord I.calldata 228).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeReadCalldataAddressRevert h₁₀ hr
      (by simp [setupDecodeReceiverSaved]; omega))
  obtain ⟨_, _, h₁₁⟩ := safeReadCalldataAddress h₁₀ hr
    (by simp [setupDecodeReceiverSaved]; omega) (by jump_dest)
  obtain ⟨k', C', h₁₂⟩ := safeSetupDecodeFinish h₁₁ (by omega) hret
  exact Or.inr ⟨n, len, k', C', ⟨hh, hs, ho, hw, hn, hin, ht, hdo, hlw, hlen, hli, hf, hk, hr⟩,
    h₁₂⟩

end Benchmarks.Safe
