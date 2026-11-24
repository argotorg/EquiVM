import Benchmarks.Safe.V1_0227664.ExecTransactionCalldataFacts
import Benchmarks.Safe.V1_0227664.AddressCalldataRead
import Benchmarks.Safe.V1_0227664.CalldataDecodeArithmetic
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_042

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

def execDecodeTargetSaved (cd : ByteArray) (ret : UInt256) (R : List UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
    ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def execDecodeDataSaved (cd : ByteArray) (ret : UInt256) (R : List UInt256) : List UInt256 :=
  [calldataWord cd 68, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
    calldataWord cd 36, calldataWord cd 4, ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def execDecodeOperationSaved (cd : ByteArray) (len : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, UInt256.ofNat len,
    UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 36, calldataWord cd 4,
    ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def execDecodeTokenSaved (cd : ByteArray) (len : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, ⟨0⟩, calldataWord cd 196, calldataWord cd 164, calldataWord cd 132,
    calldataWord cd 100, UInt256.ofNat len, UInt256.ofNat (execTransactionDataStart cd),
    calldataWord cd 36, calldataWord cd 4, ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def execDecodeReceiverSaved (cd : ByteArray) (len : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, calldataWord cd 228, calldataWord cd 196, calldataWord cd 164,
    calldataWord cd 132, calldataWord cd 100, UInt256.ofNat len,
    UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 36, calldataWord cd 4,
    ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def execDecodeSignaturesSaved (cd : ByteArray) (len : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [calldataWord cd 292, ⟨0⟩, calldataWord cd 260, calldataWord cd 228, calldataWord cd 196,
    calldataWord cd 164, calldataWord cd 132, calldataWord cd 100, UInt256.ofNat len,
    UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 36, calldataWord cd 4,
    ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def execTransactionDecodedStack (cd : ByteArray) (len : Nat) (ptr : UInt256)
    (R : List UInt256) : List UInt256 :=
  [ptr, calldataWord cd 260, calldataWord cd 228, calldataWord cd 196, calldataWord cd 164,
    calldataWord cd 132, calldataWord cd 100, UInt256.ofNat len,
    UInt256.ofNat (execTransactionDataStart cd), calldataWord cd 36, calldataWord cd 4] ++ R

set_option maxRecDepth 100000

theorem safeExecDecodeTargetStart {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9530⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 320) = ⟨0⟩)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8719⟩
      (⟨4⟩ :: ⟨9566⟩ :: execDecodeTargetSaved I.calldata ret R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9530_taken (by simp; omega)
    (by rw [hc]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_9557 (by simp; omega) (by jump_dest) h₁
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeDataStart {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9566⟩
      (calldataWord I.calldata 4 :: execDecodeTargetSaved I.calldata ret R) mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8777⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨9611⟩ :: execDecodeDataSaved I.calldata ret R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_9566_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 68) _) ≠ _
    rw [hmax, ugt_zero ho]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_9599 (by simp; omega) (by jump_dest) h₁
  have hoff : (⟨4⟩ : UInt256) + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 68).toNat (by change _ < 2 ^ 256; omega)
  simp only [safeRuntime_block_9599_stack, safeRuntime_block_9566_taken_stack] at h₂
  change (⟨4⟩ : UInt256) + calldataWord I.calldata 68 = _ at hoff
  change RD fork safeBytecode I g s0 ⟨8777⟩
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 68) :: UInt256.ofNat I.calldata.size ::
      ⟨9611⟩ :: execDecodeDataSaved I.calldata ret R) mem aw rdata σ _ _ at h₂
  rw [hoff] at h₂
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeOperationStart {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9611⟩
      (UInt256.ofNat len :: UInt256.ofNat (execTransactionDataStart I.calldata) ::
        execDecodeDataSaved I.calldata ret R) mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨9241⟩
      (⟨100⟩ :: ⟨9630⟩ :: execDecodeOperationSaved I.calldata len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9611 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

theorem safeExecDecodeTokenStart {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9630⟩
      (calldataWord I.calldata 100 :: execDecodeOperationSaved I.calldata len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8719⟩
      (⟨228⟩ :: ⟨9665⟩ :: execDecodeTokenSaved I.calldata len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9630 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

theorem safeExecDecodeReceiverStart {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9665⟩
      (calldataWord I.calldata 228 :: execDecodeTokenSaved I.calldata len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8719⟩
      (⟨260⟩ :: ⟨9680⟩ :: execDecodeReceiverSaved I.calldata len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9665 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

theorem safeExecDecodeSignaturesStart {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9680⟩
      (calldataWord I.calldata 260 :: execDecodeReceiverSaved I.calldata len ret R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 292).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8865⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 292).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨9719⟩ :: execDecodeSignaturesSaved I.calldata len ret R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_9680_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 292) _) ≠ _
    rw [hmax, ugt_zero ho]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_9707 (by simp; omega) (by jump_dest) h₁
  have hoff : (⟨4⟩ : UInt256) + calldataWord I.calldata 292 =
      UInt256.ofNat (4 + (calldataWord I.calldata 292).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 292).toNat (by change _ < 2 ^ 256; omega)
  simp only [safeRuntime_block_9707_stack, safeRuntime_block_9680_taken_stack] at h₂
  change RD fork safeBytecode I g s0 ⟨8865⟩
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 292) :: UInt256.ofNat I.calldata.size ::
      ⟨9719⟩ :: execDecodeSignaturesSaved I.calldata len ret R) mem aw rdata σ _ _ at h₂
  rw [hoff] at h₂
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeFinish {I g s0 σ k C aw mem rdata len} {ptr ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9719⟩
      (ptr :: execDecodeSignaturesSaved I.calldata len ret R) mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (execTransactionDecodedStack I.calldata len ptr R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_9719 (by change R.length + 16 ≤ 1024; omega) hret h
  exact ⟨_, _, h₁⟩

end Benchmarks.Safe.V1_0227664
