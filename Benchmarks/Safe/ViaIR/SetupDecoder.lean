import Benchmarks.Safe.ViaIR.SetupDecodeScalars
import Benchmarks.Safe.ViaIR.SetupDecodeOwnersEvidence
import Benchmarks.Safe.ViaIR.CalldataBytesDecoder

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

theorem safeDecodeSetupValid {I g s0 σ k C aw mem rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2980⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hb : SetupCalldataBounds I.calldata n len)
    (hov : R.length + 24 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k' C' := by
  obtain ⟨_, _, h₁⟩ := safeSetupDecodeOwnersValid h hb.head hb.small hb.ownersOffset
    hb.ownersWord hb.ownersLength hb.ownersEnd (by simp; omega)
  obtain ⟨_, _, h₂⟩ := safeSetupDecodeTargetStart h₁ hb.target (by omega)
  obtain ⟨_, _, h₃⟩ := safeSetupDecodeDataStart h₂ hb.dataOffset (by omega)
  obtain ⟨_, _, h₄⟩ := safeDecodeCalldataBytesValid h₃ hb.dataWord hb.dataEnd
    hb.small hb.dataLength (by simp [setupDecodeDataSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₅⟩ := safeSetupDecodeFallbackStart h₄ hb.fallbackHandler (by omega)
  obtain ⟨_, _, h₆⟩ := safeSetupDecodeTokenStart h₅ hb.paymentToken (by omega)
  obtain ⟨_, _, h₇⟩ := safeSetupDecodeReceiverStart h₆ (by omega)
  exact safeSetupDecodeFinish h₇ hb.paymentReceiver (by omega)

theorem safeDecodeSetupEvidence {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2980⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 24 ≤ 1024) :
    RDrev fork safeBytecode g s0 ∨ ∃ n len k' C', SetupCalldataBounds I.calldata n len ∧
      RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
        mem aw rdata σ k' C' := by
  obtain hr | ⟨n, _, _, hh, hs, ho, hw, hn, hin, h₁⟩ :=
    safeSetupDecodeOwnersEvidence h hlong hsize (by omega)
  · exact Or.inl hr
  by_cases ht : (calldataWord I.calldata 68).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeSetupDecodeTargetRevert h₁ ht (by omega))
  obtain ⟨_, _, h₂⟩ := safeSetupDecodeTargetStart h₁ ht (by omega)
  by_cases hdo : (calldataWord I.calldata 100).toNat ≤ 2 ^ 64 - 1
  swap
  · exact Or.inl (safeSetupDecodeDataOffsetRevert h₂ hdo (by omega))
  obtain ⟨_, _, h₃⟩ := safeSetupDecodeDataStart h₂ hdo (by omega)
  obtain hr | ⟨len, _, _, hlw, hlen, _, hli, h₄⟩ :=
    safeDecodeCalldataBytesEvidence h₃ (by omega) hsize
      (by simp [setupDecodeDataSaved]; omega) (by jump_dest)
  · exact Or.inl hr
  by_cases hf : (calldataWord I.calldata 132).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeSetupDecodeFallbackRevert h₄ hf (by omega))
  obtain ⟨_, _, h₅⟩ := safeSetupDecodeFallbackStart h₄ hf (by omega)
  by_cases hk : (calldataWord I.calldata 164).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeSetupDecodeTokenRevert h₅ hk (by omega))
  obtain ⟨_, _, h₆⟩ := safeSetupDecodeTokenStart h₅ hk (by omega)
  obtain ⟨_, _, h₇⟩ := safeSetupDecodeReceiverStart h₆ (by omega)
  by_cases hr : (calldataWord I.calldata 228).toNat < EVM.addressModulus
  swap
  · exact Or.inl (safeSetupDecodeReceiverRevert h₇ hr (by omega))
  obtain ⟨k', C', h₈⟩ := safeSetupDecodeFinish h₇ hr (by omega)
  exact Or.inr ⟨n, len, k', C', ⟨hh, hs, ho, hw, hn, hin, ht, hdo, hlw, hlen, hli, hf, hk, hr⟩,
    h₈⟩

end Benchmarks.Safe.ViaIR
