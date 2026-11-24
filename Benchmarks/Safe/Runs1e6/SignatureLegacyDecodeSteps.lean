import Benchmarks.Safe.Runs1e6.SignatureLegacyCalldata
import Benchmarks.Safe.Runs1e6.CalldataBytesDecoder
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_040
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_041
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

def signatureLegacyDecodePC (counted : Bool) : UInt256 := if counted then ⟨11953⟩ else ⟨12735⟩
def signatureLegacyOffsetPC (counted : Bool) : UInt256 := if counted then ⟨11973⟩ else ⟨12754⟩
def signatureLegacyDataPC (counted : Bool) : UInt256 := if counted then ⟨12014⟩ else ⟨12795⟩

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
    (UInt256.ofNat 18446744073709551615))

theorem signatureOffsetGuardOk {w : UInt256} (h : w.toNat ≤ 2 ^ 64 - 1) :
    signatureOffsetGuard w ≠ ⟨0⟩ := by
  have hm : UInt256.ofNat 18446744073709551615 = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  rw [signatureOffsetGuard, hm, ugt_zero h]
  decide

theorem signatureOffsetGuardBad {w : UInt256} (h : 2 ^ 64 - 1 < w.toNat) :
    signatureOffsetGuard w = ⟨0⟩ := by
  have hm : UInt256.ofNat 18446744073709551615 = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
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
    have h₁ := safeRuntime_block_12735_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_12751 (by
      simp only [safeRuntime_block_12735_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_11953_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_11970 (by
      simp only [safeRuntime_block_11953_fallthrough_stack, List.length_cons]; omega) h₁

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
    have h₁ := safeRuntime_block_12735_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    exact ⟨_, _, h₁⟩
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_11953_taken (by simp; omega) (by rw [hc]; decide)
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
    have h₁ := safeRuntime_block_12754_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_12780 (by
      simp only [safeRuntime_block_12754_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_11973_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_11999 (by
      simp only [safeRuntime_block_11973_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeSignatureLegacyToData (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted stop ret R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 36).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11639⟩
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
    have h₁ := safeRuntime_block_12754_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_12783 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_12783_stack, safeRuntime_block_12754_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    simp only [signatureLegacyOffsetPC, signatureLegacyInitialStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_11973_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_12002 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_12002_stack, safeRuntime_block_11973_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩

end Benchmarks.Safe.Runs1e6
