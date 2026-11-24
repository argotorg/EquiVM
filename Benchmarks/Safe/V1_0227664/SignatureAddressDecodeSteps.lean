import Benchmarks.Safe.V1_0227664.SignatureAddressCalldata
import Benchmarks.Safe.V1_0227664.Decoders
import Benchmarks.Safe.V1_0227664.MemoryBytesDecodeEvidence
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_040
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_046
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_047

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

set_option maxRecDepth 100000

def signatureDecodePC (counted : Bool) : UInt256 := if counted then ⟨9122⟩ else ⟨10608⟩
def signatureAddressPC (counted : Bool) : UInt256 := if counted then ⟨9152⟩ else ⟨10637⟩
def signatureBytesPC (counted : Bool) : UInt256 := if counted then ⟨9197⟩ else ⟨10682⟩

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
    have h₁ := safeRuntime_block_10608_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_10623 (by
      simp only [safeRuntime_block_10608_fallthrough_stack, List.length_cons]; omega) h₁
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_9122_fallthrough (by simp; omega) (by rw [hc]; decide) h
    exact safeRuntime_block_9138 (by
      simp only [safeRuntime_block_9122_fallthrough_stack, List.length_cons]; omega) h₁

theorem safeSignatureDecodeAddress (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureDecodePC counted) (⟨4⟩ :: stop :: ret :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub stop ⟨4⟩) (UInt256.ofNat (signatureAddressHead counted)) = ⟨0⟩)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8699⟩
      (calldataWord I.calldata 4 :: signatureAddressPC counted ::
        signatureAddressStack counted I.calldata stop ret R) mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    simp only [signatureAddressHead, Bool.false_eq_true, if_false] at hc
    have h₁ := safeRuntime_block_10608_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    have h₂ := safeRuntime_block_10626 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, h₂⟩
  | true =>
    simp only [signatureAddressHead, if_true] at hc
    have h₁ := safeRuntime_block_9122_taken (by simp; omega) (by rw [hc]; decide)
      (by jump_dest) h
    have h₂ := safeRuntime_block_9141 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, h₂⟩

set_option maxHeartbeats 1000000 in
theorem safeSignatureDecodeOffsetRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureAddressPC counted)
      (signatureAddressStack counted I.calldata stop ret R) mem aw rdata σ k C)
    (hoff : 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat)
    (hov : R.length + 18 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hgt : UInt256.gt (calldataWord I.calldata 68) (UInt256.ofNat (2 ^ 64 - 1)) = ⟨1⟩ :=
    ugt_one hoff
  have hcond : UInt256.isZero (UInt256.gt (calldataWord I.calldata 68)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1))) = ⟨0⟩ := by
    rw [hmax, hgt]; decide
  cases counted with
  | false =>
    simp only [signatureAddressPC, signatureAddressStack, Bool.false_eq_true, if_false,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_10637_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_10667 (by
      simp only [safeRuntime_block_10637_fallthrough_stack, List.length_cons, List.length_append,
        List.length_nil]; omega) h₁
  | true =>
    simp only [signatureAddressPC, signatureAddressStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_9152_fallthrough (by simp; omega) (by exact hcond) h
    exact safeRuntime_block_9182 (by
      simp only [safeRuntime_block_9152_fallthrough_stack, List.length_cons, List.length_append,
        List.length_nil]; omega) h₁

set_option maxHeartbeats 1000000 in
theorem safeSignatureDecodeBytes (counted : Bool)
    {I g s0 σ k C aw mem rdata stop ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureAddressPC counted)
      (signatureAddressStack counted I.calldata stop ret R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8865⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) :: stop :: signatureBytesPC counted ::
        signatureBytesSaved counted I.calldata stop ret R) mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hgt : UInt256.gt (calldataWord I.calldata 68) (UInt256.ofNat (2 ^ 64 - 1)) = ⟨0⟩ :=
    ugt_zero hoff
  have hcond : UInt256.isZero (UInt256.gt (calldataWord I.calldata 68)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1))) ≠ ⟨0⟩ := by
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
    have h₁ := safeRuntime_block_10637_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_10670 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_10670_stack, safeRuntime_block_10637_taken_stack,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 64).toNat = 68 by decide +kernel,
      show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₂
    simp only [calldataWord] at hadd
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    simp only [signatureAddressPC, signatureAddressStack, if_true,
      List.cons_append, List.nil_append] at h
    have h₁ := safeRuntime_block_9152_taken (by simp; omega) (by exact hcond) (by jump_dest) h
    have h₂ := safeRuntime_block_9185 (by simp; omega) (by jump_dest) h₁
    simp only [safeRuntime_block_9185_stack, safeRuntime_block_9152_taken_stack,
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
    have h₁ := safeRuntime_block_10682 (by simp; omega) hret h
    exact ⟨_, _, h₁⟩
  | true =>
    have h₁ := safeRuntime_block_9197 (by simp; omega) hret h
    simp only [safeRuntime_block_9197_stack,
      show (UInt256.ofNat 96 + (⟨4⟩ : UInt256)).toNat = 100 by decide +kernel] at h₁
    exact ⟨_, _, h₁⟩

end Benchmarks.Safe.V1_0227664
