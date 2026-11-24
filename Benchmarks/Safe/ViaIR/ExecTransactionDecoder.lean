import Benchmarks.Safe.ViaIR.ExecTransactionDecodeSteps
import Benchmarks.Safe.ViaIR.CalldataBytesDecoder
import Benchmarks.Safe.ViaIR.MemoryBytesDecodeValid

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000 in
theorem safeDecodeExecTransactionValid {I g s0 σ k C aw rdata dataLen sigLen}
    {scratch : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4354⟩ (scratch :: R) solcFreePtrMem aw rdata σ k C)
    (hb : ExecTransactionCalldataBounds I.calldata dataLen sigLen)
    (ho : (calldataWord I.calldata 100).toNat < 2) (hn : sigLen ≤ 2 ^ 64 - 192)
    (hov : R.length + 28 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨4469⟩
      (execTransactionDecodedStack I.calldata dataLen ⟨128⟩ R)
      (memoryBytesDecoded (execTransactionCalldataInput I.calldata dataLen sigLen).signatures)
      aw' rdata σ k' C' := by
  obtain ⟨_, _, h₁⟩ := safeExecDecodeTargetStart h
    (solcDecodeLenCheckOk hb.head
      (by change I.calldata.size < 2 ^ 255 + 4; have := hb.small; omega)
      (lt_size_of_lt_sign hb.small) (by decide))
    (by have := hb.head; omega) (lt_size_of_lt_sign hb.small) (by omega)
  obtain ⟨_, _, h₂⟩ := safeDecodeAddress h₁ (by simp; omega) hb.target (by jump_dest)
  obtain ⟨_, _, h₃⟩ := safeExecDecodeDataStart h₂ hb.dataOffset (by omega)
  obtain ⟨_, _, h₄⟩ := safeDecodeCalldataBytesValid h₃ hb.dataWord hb.dataEnd
    hb.small hb.dataLength (by simp [execDecodeDataSaved]; omega) (by jump_dest)
  obtain ⟨_, _, h₅⟩ := safeExecDecodeOperationStart h₄ ho (by omega)
  obtain ⟨_, _, h₆⟩ := safeExecDecodeTokenStart h₅ (by omega)
  obtain ⟨_, _, h₇⟩ := safeExecDecodeReceiverStart h₆ hb.gasToken (by omega)
  obtain ⟨_, _, h₈⟩ := safeExecDecodeReceiverFinish h₇ hb.refundReceiver (by omega)
  obtain ⟨_, _, h₉⟩ := safeExecDecodeSignaturesStart h₈ hb.sigOffset (by omega)
  obtain ⟨aw', k', C', h₁₀⟩ := safeDecodeMemoryBytesValid h₉ hb.sigWord hb.sigEnd hb.small hn
    (by simp [execDecodeSignaturesSaved, execDecodeReceiverSaved]; omega) (by jump_dest)
  exact ⟨aw', k', C', h₁₀⟩

end Benchmarks.Safe.ViaIR
