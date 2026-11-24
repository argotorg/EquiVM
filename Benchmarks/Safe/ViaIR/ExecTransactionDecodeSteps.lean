import Benchmarks.Safe.ViaIR.ExecTransactionCalldataFacts
import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.CalldataDecodeArithmetic
import Benchmarks.Safe.ViaIR.IRLengthCheck
import Benchmarks.Safe.ViaIR.Blocks.Runtime_020
import Benchmarks.Safe.ViaIR.Blocks.Runtime_021

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def execDecodeDataSaved (cd : ByteArray) (R : List UInt256) : List UInt256 :=
  calldataWord cd 4 :: R

def execDecodeOperationSaved (cd : ByteArray) (len : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat len, UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 4] ++ R

def execDecodeTokenSaved (cd : ByteArray) (len : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 4, UInt256.ofNat len] ++ R

def execDecodeReceiverSaved (cd : ByteArray) (len : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 228,
    calldataWord cd 4, UInt256.ofNat len] ++ R

def execDecodeSignaturesSaved (cd : ByteArray) (len : Nat) (R : List UInt256) : List UInt256 :=
  calldataWord cd 260 :: execDecodeReceiverSaved cd len R

def execTransactionDecodedStack (cd : ByteArray) (len : Nat) (ptr : UInt256)
    (R : List UInt256) : List UInt256 :=
  ptr :: execDecodeSignaturesSaved cd len R

set_option maxRecDepth 2000

theorem safeExecDecodeTargetStart {I g s0 σ k C aw mem rdata} {scratch : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4354⟩ (scratch :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 320) = ⟨0⟩)
    (hlong : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6952⟩ (⟨4376⟩ :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_4354_fallthrough (by simp; omega)
    (by rw [safeIRArgumentSizeSub hlong hsize]; exact hc) h
  have h₂ := safeRuntime_block_4369
    (by simp [safeRuntime_block_4354_fallthrough_stack]; omega) (by jump_dest) h₁
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeDataStart {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4376⟩
      (calldataWord I.calldata 4 :: R) mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7083⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨4407⟩ :: execDecodeDataSaved I.calldata R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_4376_fallthrough (by simp; omega) (by
    change UInt256.gt (calldataWord I.calldata 68) _ = _
    rw [hmax, ugt_zero (by exact ho)]; rfl) h
  have h₂ := safeRuntime_block_4394 (by simp; omega) (by jump_dest) h₁
  have hoff : UInt256.ofNat 4 + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 68).toNat (by change _ < 2 ^ 256; omega)
  change RD fork safeBytecode I g s0 ⟨7083⟩
    ((UInt256.ofNat 4 + calldataWord I.calldata 68) :: UInt256.ofNat I.calldata.size ::
      ⟨4407⟩ :: execDecodeDataSaved I.calldata R) mem aw rdata σ _ _ at h₂
  rw [hoff] at h₂
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeOperationStart {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4407⟩
      (execDecodeOperationSaved I.calldata len R) mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 100).toNat < 2) (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨4421⟩
      (execDecodeTokenSaved I.calldata len R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_4407_fallthrough (by simp; omega) (by
    change UInt256.isZero (UInt256.lt (calldataWord I.calldata 100) ⟨2⟩) = _
    rw [ult_one (by exact ho)]; rfl) h
  exact ⟨_, _, h₁⟩

theorem safeExecDecodeTokenStart {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4421⟩
      (execDecodeTokenSaved I.calldata len R) mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6974⟩
      (⟨4428⟩ :: execDecodeTokenSaved I.calldata len R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_4421 (by simp [execDecodeTokenSaved]; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

theorem safeExecDecodeReceiverStart {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6974⟩
      (⟨4428⟩ :: execDecodeTokenSaved I.calldata len R) mem aw rdata σ k C)
    (hc : (calldataWord I.calldata 228).toNat < EVM.addressModulus)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7018⟩
      (⟨4437⟩ :: execDecodeReceiverSaved I.calldata len R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_6974_fallthrough (by simp [execDecodeTokenSaved]; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 228)
      (UInt256.land (calldataWord I.calldata 228) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hc]; exact u256_sub_self _) h
  have h₂ := safeRuntime_block_6995 (by simp [execDecodeTokenSaved]; omega)
    (by jump_dest) h₁
  have h₃ := safeRuntime_block_4428 (by simp; omega) (by jump_dest) h₂
  exact ⟨_, _, h₃⟩

theorem safeExecDecodeReceiverFinish {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7018⟩
      (⟨4437⟩ :: execDecodeReceiverSaved I.calldata len R) mem aw rdata σ k C)
    (hc : (calldataWord I.calldata 260).toNat < EVM.addressModulus)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨4437⟩
      (execDecodeSignaturesSaved I.calldata len R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_7018_fallthrough (by simp [execDecodeReceiverSaved]; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 260)
      (UInt256.land (calldataWord I.calldata 260) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hc]; exact u256_sub_self _) h
  have h₂ := safeRuntime_block_7040 (by simp [execDecodeReceiverSaved]; omega)
    (by jump_dest) h₁
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeSignaturesStart {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4437⟩
      (execDecodeSignaturesSaved I.calldata len R) mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 292).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7262⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 292).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨4469⟩ :: execDecodeSignaturesSaved I.calldata len R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_4437_fallthrough
    (by simp [execDecodeSignaturesSaved, execDecodeReceiverSaved]; omega) (by
      change UInt256.gt (calldataWord I.calldata 292) _ = _
      rw [hmax, ugt_zero (by exact ho)]; rfl) h
  have h₂ := safeRuntime_block_4456
    (by simp [execDecodeSignaturesSaved, execDecodeReceiverSaved]; omega) (by jump_dest) h₁
  have hoff : UInt256.ofNat 4 + calldataWord I.calldata 292 =
      UInt256.ofNat (4 + (calldataWord I.calldata 292).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 292).toNat (by change _ < 2 ^ 256; omega)
  change RD fork safeBytecode I g s0 ⟨7262⟩
    ((UInt256.ofNat 4 + calldataWord I.calldata 292) :: UInt256.ofNat I.calldata.size ::
      ⟨4469⟩ :: execDecodeSignaturesSaved I.calldata len R) mem aw rdata σ _ _ at h₂
  rw [hoff] at h₂
  exact ⟨_, _, h₂⟩

end Benchmarks.Safe.ViaIR
