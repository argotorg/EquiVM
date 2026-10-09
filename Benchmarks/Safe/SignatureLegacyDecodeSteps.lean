import Benchmarks.Safe.SignatureLegacyCalldata
import Benchmarks.Safe.CalldataBytesDecoder
import Benchmarks.Safe.Blocks.Runtime_041
import Benchmarks.Safe.Blocks.Runtime_044

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureLegacyDecodePC (counted : Bool) : UInt256 := if counted then ⟨9379⟩ else ⟨10125⟩
def signatureLegacyOffsetPC (counted : Bool) : UInt256 := if counted then ⟨9399⟩ else ⟨10144⟩
def signatureLegacyDataPC (counted : Bool) : UInt256 := if counted then ⟨9439⟩ else ⟨10184⟩

def signatureLegacyInitialStack (counted : Bool) (stop ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  (if counted then [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] else [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩]) ++
    [⟨4⟩, stop, ret] ++ R

def signatureLegacyDataSaved (counted : Bool) (cd : ByteArray) (stop ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  calldataWord cd 36 :: (if counted then [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] else [⟨0⟩, ⟨0⟩, ⟨0⟩]) ++
    [calldataWord cd 4, ⟨4⟩, stop, ret] ++ R

-- LIBRARY CANDIDATE: the solc uint64 offset guard and its two branches.
def signatureOffsetGuard (w : UInt256) : UInt256 :=
  UInt256.isZero (UInt256.gt w
    (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64)) (UInt256.ofNat 1)))

theorem signatureOffsetGuardOk {w : UInt256} (h : w.toNat ≤ 2 ^ 64 - 1) :
    signatureOffsetGuard w ≠ ⟨0⟩ := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  rw [signatureOffsetGuard, hm, ugt_zero h]
  decide

theorem signatureOffsetGuardBad {w : UInt256} (h : 2 ^ 64 - 1 < w.toNat) :
    signatureOffsetGuard w = ⟨0⟩ := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hg : UInt256.gt w (UInt256.ofNat (2 ^ 64 - 1)) = ⟨1⟩ := ugt_one h
  rw [signatureOffsetGuard, hm, hg]
  decide

-- LIBRARY CANDIDATE: adding the selector length to a bounded ABI relative offset.
theorem signatureOffsetAdd {w : UInt256} (h : w.toNat ≤ 2 ^ 64 - 1) :
    (⟨4⟩ : UInt256) + w = UInt256.ofNat (4 + w.toNat) := by
  apply u256_inj
  rw [uadd_toNat, ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
  change (4 + w.toNat) % UInt256.size = _
  exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)

theorem safeSignatureLegacyHeaderRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyDecodePC counted) (⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat (signatureAddressHead counted)) = ⟨1⟩)
    (hov : R.length + 20 ≤ 1024) : RDrev safeBytecode g s0 := by
  cases counted with
  | false =>
    simp only [signatureAddressHead, Bool.false_eq_true, if_false] at hc
    have h₁ := safeRuntime_block_10125_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_10141 (by
      simp only [safeRuntime_block_10125_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_9379_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_9396 (by
      simp only [safeRuntime_block_9379_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeSignatureLegacyStart (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyDecodePC counted) (⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat (signatureAddressHead counted)) = ⟨0⟩)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted stop ret R) mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    simp only [signatureAddressHead, Bool.false_eq_true, if_false] at hc
    have h₁ := safeRuntime_block_10125_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    exact ⟨_, _, h₁⟩
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_9379_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    exact ⟨_, _, h₁⟩

theorem safeSignatureLegacyDataOffsetRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted stop ret R) mem aw rdata σ k C)
    (hoff : 2 ^ 64 - 1 < (calldataWord I.calldata 36).toNat)
    (hov : R.length + 20 ≤ 1024) : RDrev safeBytecode g s0 := by
  have hcond := signatureOffsetGuardBad hoff
  cases counted with
  | false =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_10144_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_10169 (by
      simp only [safeRuntime_block_10144_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_9399_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_9424 (by
      simp only [safeRuntime_block_9399_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeSignatureLegacyToData (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted stop ret R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 36).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9154⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 36).toNat) :: stop ::
        signatureLegacyDataPC counted :: signatureLegacyDataSaved counted I.calldata stop ret R)
      mem aw rdata σ k' C' := by
  have hcond := signatureOffsetGuardOk hoff
  have hadd := signatureOffsetAdd hoff
  simp only [calldataWord] at hadd
  cases counted with
  | false =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_10144_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_10172 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_10172_stack, safeRuntime_block_10144_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_9399_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_9427 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_9427_stack, safeRuntime_block_9399_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩

end Benchmarks.Safe
