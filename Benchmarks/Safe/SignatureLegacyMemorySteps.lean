import Benchmarks.Safe.SignatureLegacyDecodeSteps
import Benchmarks.Safe.Blocks.Runtime_045

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureLegacyBytesPC (counted : Bool) : UInt256 := if counted then ⟨9481⟩ else ⟨10226⟩

def signatureLegacyBytesSaved (counted : Bool) (cd : ByteArray)
    (stop ret dataOff dataLen : UInt256) (R : List UInt256) : List UInt256 :=
  calldataWord cd 68 :: (if counted then [⟨0⟩, ⟨0⟩] else [⟨0⟩]) ++
    [dataLen, dataOff, calldataWord cd 4, ⟨4⟩, stop, ret] ++ R

def signatureLegacyDecodedStack (counted : Bool) (cd : ByteArray)
    (dataOff dataLen : UInt256) (R : List UInt256) : List UInt256 :=
  (if counted then [calldataWord cd 100] else []) ++
    [⟨128⟩, dataLen, dataOff, calldataWord cd 4] ++ R

theorem safeSignatureLegacyBytesOffsetRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret dataOff dataLen} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyDataPC counted)
      (dataLen :: dataOff :: signatureLegacyDataSaved counted I.calldata stop ret R)
      mem aw rdata σ k C)
    (hoff : 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat)
    (hov : R.length + 20 ≤ 1024) : RDrev safeBytecode g s0 := by
  have hcond := signatureOffsetGuardBad hoff
  cases counted with
  | false =>
    simp only [signatureLegacyDataPC, signatureLegacyDataSaved, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_10184_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_10211 (by
      simp only [safeRuntime_block_10184_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureLegacyDataPC, signatureLegacyDataSaved, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_9439_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_9466 (by
      simp only [safeRuntime_block_9439_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeSignatureLegacyToBytes (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret dataOff dataLen} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyDataPC counted)
      (dataLen :: dataOff :: signatureLegacyDataSaved counted I.calldata stop ret R)
      mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9242⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) :: stop ::
        signatureLegacyBytesPC counted ::
        signatureLegacyBytesSaved counted I.calldata stop ret dataOff dataLen R)
      mem aw rdata σ k' C' := by
  have hcond := signatureOffsetGuardOk hoff
  have hadd := signatureOffsetAdd hoff
  simp only [calldataWord] at hadd
  cases counted with
  | false =>
    simp only [signatureLegacyDataPC, signatureLegacyDataSaved, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_10184_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_10214 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_10214_stack, safeRuntime_block_10184_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 64).toNat = 68 by decide +kernel] at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    simp only [signatureLegacyDataPC, signatureLegacyDataSaved, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_9439_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_9469 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_9469_stack, safeRuntime_block_9439_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 64).toNat = 68 by decide +kernel] at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩

theorem safeSignatureLegacyDecodeFinish (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret dataOff dataLen} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyBytesPC counted)
      (⟨128⟩ :: signatureLegacyBytesSaved counted I.calldata stop ret dataOff dataLen R)
      mem aw rdata σ k C)
    (hov : R.length + 20 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret
      (signatureLegacyDecodedStack counted I.calldata dataOff dataLen R) mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_10226 (by simp; omega) hret h
    exact ⟨_, _, h₁⟩
  | true =>
    have h₁ := safeRuntime_block_9481 (by simp; omega) hret h
    simp only [safeRuntime_block_9481_stack,
      show (UInt256.ofNat 96 + (⟨4⟩ : UInt256)).toNat = 100 by decide +kernel] at h₁
    exact ⟨_, _, h₁⟩

end Benchmarks.Safe
