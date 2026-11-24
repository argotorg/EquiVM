import Benchmarks.Safe.Runs1e6.SignatureAddressCalldata
import Benchmarks.Safe.Runs1e6.Decoders
import Benchmarks.Safe.Runs1e6.MemoryBytesDecodeEvidence
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_041
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_048

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

def signatureDecodePC (counted : Bool) : UInt256 := if counted then ⟨12075⟩ else ⟨13639⟩
def signatureAddressPC (counted : Bool) : UInt256 := if counted then ⟨12105⟩ else ⟨13668⟩
def signatureBytesPC (counted : Bool) : UInt256 := if counted then ⟨12151⟩ else ⟨13714⟩

def signatureAddressStack (counted : Bool) (cd : ByteArray) (stop ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  calldataWord cd 4 :: (if counted then [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩] else [⟨0⟩, ⟨0⟩, ⟨0⟩]) ++
    [⟨4⟩, stop, ret] ++ R

def signatureBytesSaved (counted : Bool) (cd : ByteArray) (stop ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  calldataWord cd 68 :: (if counted then [⟨0⟩, ⟨0⟩] else [⟨0⟩]) ++
    [calldataWord cd 36, calldataWord cd 4, ⟨4⟩, stop, ret] ++ R

def signatureDecodedStack (counted : Bool) (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  (if counted then [calldataWord cd 100] else []) ++
    [⟨128⟩, calldataWord cd 36, calldataWord cd 4] ++ R

theorem safeSignatureDecodeHeaderRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureDecodePC counted) (⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat (signatureAddressHead counted)) = ⟨1⟩)
    (hov : R.length + 18 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  cases counted with
  | false =>
    simp only [signatureAddressHead, Bool.false_eq_true, if_false] at hc
    have h₁ := safeRuntime_block_13639_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_13654 (by
      simp only [safeRuntime_block_13639_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_12075_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_12091 (by
      simp only [safeRuntime_block_12075_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeSignatureDecodeAddress (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureDecodePC counted) (⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat (signatureAddressHead counted)) = ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11548⟩
      (calldataWord I.calldata 4 :: signatureAddressPC counted ::
        signatureAddressStack counted I.calldata stop ret R) mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    simp only [signatureAddressHead, Bool.false_eq_true, if_false] at hc
    have h₁ := safeRuntime_block_13639_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    have h₂ := safeRuntime_block_13657 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, h₂⟩
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_12075_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    have h₂ := safeRuntime_block_12094 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, h₂⟩

set_option maxHeartbeats 1000000 in
theorem safeSignatureDecodeOffsetRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureAddressPC counted)
      (signatureAddressStack counted I.calldata stop ret R) mem aw rdata σ k C)
    (hoff : 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat)
    (hov : R.length + 18 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.ofNat 18446744073709551615 = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hgt : UInt256.gt (calldataWord I.calldata 68) (UInt256.ofNat (2 ^ 64 - 1)) = ⟨1⟩ :=
    ugt_one hoff
  have hcond : UInt256.isZero (UInt256.gt (calldataWord I.calldata 68)
      (UInt256.ofNat 18446744073709551615)) = ⟨0⟩ := by
    rw [hmax, hgt]; decide
  cases counted with
  | false =>
    simp only [signatureAddressPC, signatureAddressStack, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_13668_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_13699 (by
      simp only [safeRuntime_block_13668_fallthrough_stack, List.length_cons, List.length_append,
        List.length_nil]; omega) h₁
  | true =>
    simp only [signatureAddressPC, signatureAddressStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_12105_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_12136 (by
      simp only [safeRuntime_block_12105_fallthrough_stack, List.length_cons, List.length_append,
        List.length_nil]; omega) h₁

set_option maxHeartbeats 1000000 in
theorem safeSignatureDecodeBytes (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureAddressPC counted)
      (signatureAddressStack counted I.calldata stop ret R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11753⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) :: stop :: signatureBytesPC counted ::
        signatureBytesSaved counted I.calldata stop ret R) mem aw rdata σ k' C' := by
  have hmax : UInt256.ofNat 18446744073709551615 = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hgt : UInt256.gt (calldataWord I.calldata 68) (UInt256.ofNat (2 ^ 64 - 1)) = ⟨0⟩ :=
    ugt_zero hoff
  have hcond : UInt256.isZero (UInt256.gt (calldataWord I.calldata 68)
      (UInt256.ofNat 18446744073709551615)) ≠ ⟨0⟩ := by
    rw [hmax, hgt]; decide
  have hadd : (⟨4⟩ : UInt256) + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := by
    apply u256_inj
    rw [uadd_toNat, ulit_toNat' _ (by change _ < 2 ^ 256; omega)]
    change (4 + (calldataWord I.calldata 68).toNat) % UInt256.size = _
    exact Nat.mod_eq_of_lt (by change _ < 2 ^ 256; omega)
  cases counted with
  | false =>
    simp only [signatureAddressPC, signatureAddressStack, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_13668_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_13702 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_13702_stack, safeRuntime_block_13668_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 64).toNat = 68 by decide +kernel,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    simp only [calldataWord] at hadd
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    simp only [signatureAddressPC, signatureAddressStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_12105_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_12139 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_12139_stack, safeRuntime_block_12105_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 64).toNat = 68 by decide +kernel,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    simp only [calldataWord] at hadd
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩

set_option maxHeartbeats 1000000 in
theorem safeSignatureDecodeFinish (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureBytesPC counted)
      (⟨128⟩ :: signatureBytesSaved counted I.calldata stop ret R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (signatureDecodedStack counted I.calldata R)
      mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_13714 (by simp; omega) hret h
    exact ⟨_, _, h₁⟩
  | true =>
    have h₁ := safeRuntime_block_12151 (by simp; omega) hret h
    simp only [safeRuntime_block_12151_stack,
      show (UInt256.ofNat 96 + (⟨4⟩ : UInt256)).toNat = 100 by decide +kernel] at h₁
    exact ⟨_, _, h₁⟩

end Benchmarks.Safe.Runs1e6
