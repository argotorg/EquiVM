import Benchmarks.Safe.ViaIR.SignatureAddressCalldata
import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.MemoryBytesDecodeEvidence
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_006
import Benchmarks.Safe.ViaIR.Blocks.Runtime_007
import Benchmarks.Safe.ViaIR.Blocks.Runtime_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

def signatureDecodePC (counted : Bool) : UInt256 := if counted then ⟨6514⟩ else ⟨906⟩
def signatureAddressPC (counted : Bool) : UInt256 := if counted then ⟨6533⟩ else ⟨925⟩
def signatureBytesPC (counted : Bool) : UInt256 := if counted then ⟨6568⟩ else ⟨960⟩
def signatureBodyPC (counted : Bool) : UInt256 := if counted then ⟨7531⟩ else ⟨9258⟩
def signatureReturnPC (counted : Bool) : UInt256 := if counted then ⟨109⟩ else ⟨970⟩

def signatureAddressStack (_counted : Bool) (cd : ByteArray) (scratch : UInt256)
    (R : List UInt256) : List UInt256 := calldataWord cd 4 :: scratch :: R

def signatureBytesSaved (counted : Bool) (cd : ByteArray) (scratch : UInt256)
    (R : List UInt256) : List UInt256 :=
  calldataWord cd 4 :: signatureReturnPC counted :: scratch :: R

def signatureDecodedStack (counted : Bool) (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  calldataWord cd 4 :: calldataWord cd 36 :: ⟨128⟩ ::
    (if counted then [calldataWord cd 100] else []) ++ signatureReturnPC counted :: R

theorem safeSignatureDecodeHeaderRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureDecodePC counted) (scratch :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat (signatureAddressHead counted)) = ⟨1⟩)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 18 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_906_taken (by simp; omega) (by
      rw [safeIRArgumentSizeSub hlong hsize]
      change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
        (UInt256.ofNat (signatureAddressHead false)) ≠ ⟨0⟩
      rw [hc]; decide) (by jump_dest) h
    exact safeRuntime_block_589 (by simp; omega) h₁
  | true =>
    have h₁ := safeRuntime_block_6514_taken (by simp; omega) (by
      rw [safeIRArgumentSizeSub hlong hsize]
      change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
        (UInt256.ofNat (signatureAddressHead true)) ≠ ⟨0⟩
      rw [hc]; decide) (by jump_dest) h
    exact safeRuntime_block_111 (by simp; omega) h₁

theorem safeSignatureDecodeAddress (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureDecodePC counted) (scratch :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat (signatureAddressHead counted)) = ⟨0⟩)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6952⟩ (signatureAddressPC counted :: scratch :: R)
      mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_906_fallthrough (by simp; omega) (by
      rw [safeIRArgumentSizeSub hlong hsize]; exact hc) h
    have h₂ := safeRuntime_block_918 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, h₂⟩
  | true =>
    have h₁ := safeRuntime_block_6514_fallthrough (by simp; omega) (by
      rw [safeIRArgumentSizeSub hlong hsize]; exact hc) h
    have h₂ := safeRuntime_block_6526 (by simp; omega) (by jump_dest) h₁
    exact ⟨_, _, h₂⟩

theorem safeSignatureDecodeOffsetRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureAddressPC counted)
      (signatureAddressStack counted I.calldata scratch R) mem aw rdata σ k C)
    (hoff : 2 ^ 64 - 1 < (calldataWord I.calldata 68).toNat)
    (hov : R.length + 18 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hcond : UInt256.gt (calldataWord I.calldata 68)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) ≠ ⟨0⟩ := by
    rw [hmax, ugt_one (by exact hoff)]; decide
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_925_taken (by simp; omega)
      hcond (by jump_dest) h
    exact safeRuntime_block_973 (by simp; omega) h₁
  | true =>
    have h₁ := safeRuntime_block_6533_taken (by simp; omega)
      hcond (by jump_dest) h
    exact safeRuntime_block_111 (by simp [safeRuntime_block_6533_taken_stack]; omega) h₁

theorem safeSignatureDecodeBytes (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureAddressPC counted)
      (signatureAddressStack counted I.calldata scratch R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7262⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) :: UInt256.ofNat I.calldata.size ::
        signatureBytesPC counted :: signatureBytesSaved counted I.calldata scratch R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hcond : UInt256.gt (calldataWord I.calldata 68)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = ⟨0⟩ := by
    rw [hmax, ugt_zero hoff]
  have hadd : UInt256.ofNat 4 + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := by
    conv_lhs => rw [← u256_ofNat_toNat (calldataWord I.calldata 68)]
    exact wordOfNatAdd _ _ (by change _ < 2 ^ 256; omega)
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_925_fallthrough (by simp; omega) hcond h
    have h₂ := safeRuntime_block_944 (by simp; omega) (by jump_dest) h₁
    change RD fork safeBytecode I g s0 ⟨7262⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 68) :: UInt256.ofNat I.calldata.size ::
        signatureBytesPC false :: signatureBytesSaved false I.calldata scratch R)
      mem aw rdata σ _ _ at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    have h₁ := safeRuntime_block_6533_fallthrough (by simp; omega) hcond h
    have h₂ := safeRuntime_block_6552 (by simp; omega) (by jump_dest) h₁
    change RD fork safeBytecode I g s0 ⟨7262⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 68) :: UInt256.ofNat I.calldata.size ::
        signatureBytesPC true :: signatureBytesSaved true I.calldata scratch R)
      mem aw rdata σ _ _ at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩

theorem safeSignatureDecodeFinish (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureBytesPC counted)
      (⟨128⟩ :: signatureBytesSaved counted I.calldata scratch R) mem aw rdata σ k C)
    (hov : R.length + 18 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 (signatureBodyPC counted)
      (signatureDecodedStack counted I.calldata (scratch :: R)) mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_960 (by simp; omega) (by jump_dest) h
    exact ⟨_, _, h₁⟩
  | true =>
    have h₁ := safeRuntime_block_6568 (by simp; omega) (by jump_dest) h
    exact ⟨_, _, h₁⟩

end Benchmarks.Safe.ViaIR
