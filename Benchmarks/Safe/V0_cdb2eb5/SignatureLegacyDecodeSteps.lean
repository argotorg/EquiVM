import Benchmarks.Safe.V0_cdb2eb5.SignatureLegacyCalldata
import Benchmarks.Safe.V0_cdb2eb5.CalldataBytesDecoder
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_040
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

def signatureLegacyDecodePC (counted : Bool) : UInt256 := if counted then ⟨9258⟩ else ⟨9994⟩
def signatureLegacyOffsetPC (counted : Bool) : UInt256 := if counted then ⟨9278⟩ else ⟨10013⟩
def signatureLegacyDataPC (counted : Bool) : UInt256 := if counted then ⟨9318⟩ else ⟨10053⟩

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
    (h : RD fork safeBytecode I g s0 (signatureLegacyDecodePC counted) (⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat (signatureAddressHead counted)) = ⟨1⟩)
    (hov : R.length + 20 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  cases counted with
  | false =>
    simp only [signatureAddressHead, Bool.false_eq_true, if_false] at hc
    have h₁ := safeRuntime_block_9994_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_10010 (by
      simp only [safeRuntime_block_9994_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_9258_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_9275 (by
      simp only [safeRuntime_block_9258_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeSignatureLegacyStart (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyDecodePC counted) (⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat (signatureAddressHead counted)) = ⟨0⟩)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted stop ret R) mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    simp only [signatureAddressHead, Bool.false_eq_true, if_false] at hc
    have h₁ := safeRuntime_block_9994_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    exact ⟨_, _, h₁⟩
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_9258_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    exact ⟨_, _, h₁⟩

theorem safeSignatureLegacyDataOffsetRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted stop ret R) mem aw rdata σ k C)
    (hoff : 2 ^ 64 - 1 < (calldataWord I.calldata 36).toNat)
    (hov : R.length + 20 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hcond := signatureOffsetGuardBad hoff
  cases counted with
  | false =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_10013_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_10038 (by
      simp only [safeRuntime_block_10013_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_9278_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_9303 (by
      simp only [safeRuntime_block_9278_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeSignatureLegacyToData (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted stop ret R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 36).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨9033⟩
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
    have h₁ := safeRuntime_block_10013_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_10041 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_10041_stack, safeRuntime_block_10013_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_9278_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_9306 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_9306_stack, safeRuntime_block_9278_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩

end Benchmarks.Safe.V0_cdb2eb5
