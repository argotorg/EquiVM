import Benchmarks.Safe.ViaIR.SignatureLegacyDecodeSteps
import Benchmarks.Safe.ViaIR.SignatureAddressDecodeSteps
import Benchmarks.Safe.ViaIR.Blocks.Runtime_032

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

def signatureLegacyBytesPC (counted : Bool) : UInt256 := if counted then ⟨6665⟩ else ⟨4278⟩

def signatureLegacyBytesSaved (counted : Bool) (scratch : UInt256)
    (R : List UInt256) : List UInt256 := signatureReturnPC counted :: scratch :: R

def signatureLegacyDecodedStack (counted : Bool) (I : ExecutionEnv)
    (R : List UInt256) : List UInt256 :=
  UInt256.ofNat I.source.val :: calldataWord I.calldata 4 :: ⟨128⟩ ::
    (if counted then [calldataWord I.calldata 100] else []) ++ signatureReturnPC counted :: R

theorem safeSignatureLegacyBytesOffsetRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch dataOff dataLen} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyDataPC counted)
      (dataLen :: dataOff :: signatureLegacyDataSaved counted scratch R) mem aw rdata σ k C)
    (hoff : 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat)
    (hov : R.length + 20 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hcond : UInt256.gt (calldataWord I.calldata 68)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) ≠ UInt256.ofNat 0 := by
    rw [hm, ugt_one (by exact hoff)]; decide
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_4242_taken
      (by simp [signatureLegacyDataSaved]; omega) hcond (by jump_dest) h
    exact safeRuntime_block_3913 (by simp; omega) h₁
  | true =>
    have h₁ := safeRuntime_block_6629_taken
      (by simp [signatureLegacyDataSaved]; omega) hcond (by jump_dest) h
    exact safeRuntime_block_111 (by
      simp [safeRuntime_block_6629_taken_stack, signatureLegacyDataSaved]; omega) h₁

theorem safeSignatureLegacyToBytes (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch dataOff dataLen} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyDataPC counted)
      (dataLen :: dataOff :: signatureLegacyDataSaved counted scratch R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7262⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) :: UInt256.ofNat I.calldata.size ::
        signatureLegacyBytesPC counted :: signatureLegacyBytesSaved counted scratch R)
      mem aw rdata σ k' C' := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hcond : UInt256.gt (calldataWord I.calldata 68)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = UInt256.ofNat 0 := by
    rw [hm, ugt_zero (by exact hoff)]; rfl
  have hadd : UInt256.ofNat 4 + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := signatureOffsetAdd hoff
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_4242_fallthrough
      (by simp [signatureLegacyDataSaved]; omega) hcond h
    have h₂ := safeRuntime_block_4262 (by simp [signatureLegacyDataSaved]; omega)
      (by jump_dest) h₁
    change RD fork safeBytecode I g s0 ⟨7262⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 68) :: UInt256.ofNat I.calldata.size ::
        signatureLegacyBytesPC false :: signatureLegacyBytesSaved false scratch R)
      mem aw rdata σ _ _ at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    have h₁ := safeRuntime_block_6629_fallthrough
      (by simp [signatureLegacyDataSaved]; omega) hcond h
    have h₂ := safeRuntime_block_6649 (by simp [signatureLegacyDataSaved]; omega)
      (by jump_dest) h₁
    change RD fork safeBytecode I g s0 ⟨7262⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 68) :: UInt256.ofNat I.calldata.size ::
        signatureLegacyBytesPC true :: signatureLegacyBytesSaved true scratch R)
      mem aw rdata σ _ _ at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩

theorem safeSignatureLegacyDecodeFinish (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyBytesPC counted)
      (⟨128⟩ :: signatureLegacyBytesSaved counted scratch R) mem aw rdata σ k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 (signatureBodyPC counted)
      (signatureLegacyDecodedStack counted I (scratch :: R)) mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_4278 (by simp [signatureLegacyBytesSaved]; omega)
      (by jump_dest) h
    exact ⟨_, _, h₁⟩
  | true =>
    have h₁ := safeRuntime_block_6665 (by simp [signatureLegacyBytesSaved]; omega)
      (by jump_dest) h
    exact ⟨_, _, h₁⟩

end Benchmarks.Safe.ViaIR
