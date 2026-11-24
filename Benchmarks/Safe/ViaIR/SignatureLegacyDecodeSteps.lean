import Benchmarks.Safe.ViaIR.SignatureLegacyCalldata
import Benchmarks.Safe.ViaIR.CalldataBytesDecoder
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_018
import Benchmarks.Safe.ViaIR.Blocks.Runtime_020
import Benchmarks.Safe.ViaIR.Blocks.Runtime_031

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

def signatureLegacyDecodePC (counted : Bool) : UInt256 := if counted then ⟨6587⟩ else ⟨4200⟩
def signatureLegacyOffsetPC (counted : Bool) : UInt256 := if counted then ⟨6599⟩ else ⟨4212⟩
def signatureLegacyDataPC (counted : Bool) : UInt256 := if counted then ⟨6629⟩ else ⟨4242⟩

def signatureLegacyInitialStack (_counted : Bool) (scratch : UInt256)
    (R : List UInt256) : List UInt256 := scratch :: R

def signatureLegacyDataSaved (_counted : Bool) (scratch : UInt256)
    (R : List UInt256) : List UInt256 := scratch :: R

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
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyDecodePC counted) (scratch :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat (signatureAddressHead counted)) = ⟨1⟩)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_4200_taken (by simp; omega) (by
      rw [safeIRArgumentSizeSub hlong hsize]
      change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
        (UInt256.ofNat (signatureAddressHead false)) ≠ ⟨0⟩
      rw [hc]; decide) (by jump_dest) h
    exact safeRuntime_block_589 (by simp; omega) h₁
  | true =>
    have h₁ := safeRuntime_block_6587_taken (by simp; omega) (by
      rw [safeIRArgumentSizeSub hlong hsize]
      change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
        (UInt256.ofNat (signatureAddressHead true)) ≠ ⟨0⟩
      rw [hc]; decide) (by jump_dest) h
    exact safeRuntime_block_111 (by simp; omega) h₁

theorem safeSignatureLegacyStart (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyDecodePC counted) (scratch :: R)
      mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat (signatureAddressHead counted)) = ⟨0⟩)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted scratch R) mem aw rdata σ k' C' := by
  cases counted with
  | false =>
    exact ⟨_, _, safeRuntime_block_4200_fallthrough
      (by simp [signatureLegacyInitialStack]; omega)
      (by rw [safeIRArgumentSizeSub hlong hsize]; exact hc) h⟩
  | true =>
    exact ⟨_, _, safeRuntime_block_6587_fallthrough
      (by simp [signatureLegacyInitialStack]; omega)
      (by rw [safeIRArgumentSizeSub hlong hsize]; exact hc) h⟩

theorem safeSignatureLegacyDataOffsetRevert (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted scratch R) mem aw rdata σ k C)
    (hoff : 2 ^ 64 - 1 < (calldataWord I.calldata 36).toNat)
    (hov : R.length + 20 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hcond : UInt256.gt (calldataWord I.calldata 36)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) ≠ UInt256.ofNat 0 := by
    rw [hm, ugt_one (by exact hoff)]; decide
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_4212_taken
      (by simp [signatureLegacyInitialStack]; omega) hcond (by jump_dest) h
    exact safeRuntime_block_3913 (by simp; omega) h₁
  | true =>
    have h₁ := safeRuntime_block_6599_taken
      (by simp [signatureLegacyInitialStack]; omega) hcond (by jump_dest) h
    exact safeRuntime_block_111 (by
      simp [safeRuntime_block_6599_taken_stack, signatureLegacyInitialStack]; omega) h₁

theorem safeSignatureLegacyToData (counted : Bool)
    {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 (signatureLegacyOffsetPC counted)
      (signatureLegacyInitialStack counted scratch R) mem aw rdata σ k C)
    (hoff : (calldataWord I.calldata 36).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7083⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 36).toNat) :: UInt256.ofNat I.calldata.size ::
        signatureLegacyDataPC counted :: signatureLegacyDataSaved counted scratch R)
      mem aw rdata σ k' C' := by
  have hm : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have hcond : UInt256.gt (calldataWord I.calldata 36)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = UInt256.ofNat 0 := by
    rw [hm, ugt_zero (by exact hoff)]; rfl
  have hadd : UInt256.ofNat 4 + calldataWord I.calldata 36 =
      UInt256.ofNat (4 + (calldataWord I.calldata 36).toNat) := signatureOffsetAdd hoff
  cases counted with
  | false =>
    have h₁ := safeRuntime_block_4212_fallthrough
      (by simp [signatureLegacyInitialStack]; omega) hcond h
    have h₂ := safeRuntime_block_4229
      (by simp [signatureLegacyInitialStack]; omega) (by jump_dest) h₁
    change RD fork safeBytecode I g s0 ⟨7083⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 36) :: UInt256.ofNat I.calldata.size ::
        signatureLegacyDataPC false :: signatureLegacyDataSaved false scratch R)
      mem aw rdata σ _ _ at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩
  | true =>
    have h₁ := safeRuntime_block_6599_fallthrough
      (by simp [signatureLegacyInitialStack]; omega) hcond h
    have h₂ := safeRuntime_block_6616
      (by simp [signatureLegacyInitialStack]; omega) (by jump_dest) h₁
    change RD fork safeBytecode I g s0 ⟨7083⟩
      ((UInt256.ofNat 4 + calldataWord I.calldata 36) :: UInt256.ofNat I.calldata.size ::
        signatureLegacyDataPC true :: signatureLegacyDataSaved true scratch R)
      mem aw rdata σ _ _ at h₂
    rw [hadd] at h₂
    exact ⟨_, _, h₂⟩

end Benchmarks.Safe.ViaIR
