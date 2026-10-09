import Benchmarks.Safe.ExecTransactionDecodeSteps
import Benchmarks.Safe.CalldataBytesDecoder
import Benchmarks.Safe.MemoryBytesDecodeValid

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeDecodeExecTransactionValid {I g s0 σ k C aw rdata dataLen sigLen}
    {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨9917⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hb : ExecTransactionCalldataBounds I.calldata dataLen sigLen)
    (ho : (calldataWord I.calldata 100).toNat < 2) (hn : sigLen ≤ 2 ^ 64 - 192)
    (hov : R.length + 28 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ aw' k' C', RD safeBytecode I g s0 ret
      (execTransactionDecodedStack I.calldata dataLen ⟨128⟩ R)
      (memoryBytesDecoded (execTransactionCalldataInput I.calldata dataLen sigLen).signatures)
      aw' rdata σ k' C' := by
  obtain ⟨_, _, h₁⟩ := safeExecDecodeTargetStart h
    (solcDecodeLenCheckOk hb.head
      (by change I.calldata.size < 2 ^ 255 + 4; have := hb.small; omega)
      (lt_size_of_lt_sign hb.small) (by decide)) (by omega)
  obtain ⟨_, _, h₂⟩ := safeReadCalldataAddress h₁ hb.target
    (by simp [execDecodeTargetSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₃⟩ := safeExecDecodeDataStart h₂ hb.dataOffset (by omega)
  obtain ⟨_, _, h₄⟩ := safeDecodeCalldataBytesValid h₃ hb.dataWord hb.dataEnd
    hb.small hb.dataLength (by simp [execDecodeDataSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₅⟩ := safeExecDecodeOperationStart h₄ (by omega)
  obtain ⟨_, _, h₆⟩ := safeDecodeOperation h₅ ho
    (by simp [execDecodeOperationSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₇⟩ := safeExecDecodeTokenStart h₆ (by omega)
  obtain ⟨_, _, h₈⟩ := safeReadCalldataAddress h₇ hb.gasToken
    (by simp [execDecodeTokenSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₉⟩ := safeExecDecodeReceiverStart h₈ (by omega)
  obtain ⟨_, _, h₁₀⟩ := safeReadCalldataAddress h₉ hb.refundReceiver
    (by simp [execDecodeReceiverSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₁₁⟩ := safeExecDecodeSignaturesStart h₁₀ hb.sigOffset (by omega)
  obtain ⟨aw', _, _, h₁₂⟩ := safeDecodeMemoryBytesValid h₁₁ hb.sigWord hb.sigEnd hb.small hn
    (by simp [execDecodeSignaturesSaved]; omega) (by jump_dest)
  obtain ⟨k', C', h₁₃⟩ := safeExecDecodeFinish h₁₂ (by omega) hret
  exact ⟨aw', k', C', h₁₃⟩

end Benchmarks.Safe
