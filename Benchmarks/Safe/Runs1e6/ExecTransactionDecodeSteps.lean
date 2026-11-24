import Benchmarks.Safe.Runs1e6.ExecTransactionCalldataFacts
import Benchmarks.Safe.Runs1e6.AddressCalldataRead
import Benchmarks.Safe.Runs1e6.CalldataDecodeArithmetic
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_043
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_044

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

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
    (h : RD fork safeBytecode I g s0 ⟨12525⟩
      (⟨4⟩ :: UInt256.ofNat I.calldata.size :: ret :: R) mem aw rdata σ k C)
    (hc : UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩)
      (UInt256.ofNat 320) = ⟨0⟩)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11581⟩
      (⟨4⟩ :: ⟨12561⟩ :: execDecodeTargetSaved I.calldata ret R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_12525_taken (by simp; omega)
    (by rw [hc]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_12552 (by simp; omega) (by jump_dest) h₁
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeDataStart {I g s0 σ k C aw mem rdata} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨12561⟩
      (calldataWord I.calldata 4 :: execDecodeTargetSaved I.calldata ret R) mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 68).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11639⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨12607⟩ :: execDecodeDataSaved I.calldata ret R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.ofNat 18446744073709551615 = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_12561_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 68) _) ≠ _
    rw [hmax, ugt_zero ho]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_12595 (by simp; omega) (by jump_dest) h₁
  have hoff : (⟨4⟩ : UInt256) + calldataWord I.calldata 68 =
      UInt256.ofNat (4 + (calldataWord I.calldata 68).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 68).toNat (by change _ < 2 ^ 256; omega)
  simp only [safeRuntime_block_12595_stack, safeRuntime_block_12561_taken_stack] at h₂
  change (⟨4⟩ : UInt256) + calldataWord I.calldata 68 = _ at hoff
  change RD fork safeBytecode I g s0 ⟨11639⟩
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 68) :: UInt256.ofNat I.calldata.size ::
      ⟨12607⟩ :: execDecodeDataSaved I.calldata ret R) mem aw rdata σ _ _ at h₂
  rw [hoff] at h₂
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeOperationStart {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨12607⟩
      (UInt256.ofNat len :: UInt256.ofNat (execTransactionDataStart I.calldata) ::
        execDecodeDataSaved I.calldata ret R) mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨12195⟩
      (⟨100⟩ :: ⟨12626⟩ :: execDecodeOperationSaved I.calldata len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_12607 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

theorem safeExecDecodeTokenStart {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨12626⟩
      (calldataWord I.calldata 100 :: execDecodeOperationSaved I.calldata len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11581⟩
      (⟨228⟩ :: ⟨12661⟩ :: execDecodeTokenSaved I.calldata len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_12626 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

theorem safeExecDecodeReceiverStart {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨12661⟩
      (calldataWord I.calldata 228 :: execDecodeTokenSaved I.calldata len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11581⟩
      (⟨260⟩ :: ⟨12676⟩ :: execDecodeReceiverSaved I.calldata len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_12661 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

theorem safeExecDecodeSignaturesStart {I g s0 σ k C aw mem rdata len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨12676⟩
      (calldataWord I.calldata 260 :: execDecodeReceiverSaved I.calldata len ret R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 292).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 26 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨11753⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 292).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨12716⟩ :: execDecodeSignaturesSaved I.calldata len ret R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.ofNat 18446744073709551615 = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_12676_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 292) _) ≠ _
    rw [hmax, ugt_zero ho]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_12704 (by simp; omega) (by jump_dest) h₁
  have hoff : (⟨4⟩ : UInt256) + calldataWord I.calldata 292 =
      UInt256.ofNat (4 + (calldataWord I.calldata 292).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 292).toNat (by change _ < 2 ^ 256; omega)
  simp only [safeRuntime_block_12704_stack, safeRuntime_block_12676_taken_stack] at h₂
  change RD fork safeBytecode I g s0 ⟨11753⟩
    (((⟨4⟩ : UInt256) + calldataWord I.calldata 292) :: UInt256.ofNat I.calldata.size ::
      ⟨12716⟩ :: execDecodeSignaturesSaved I.calldata len ret R) mem aw rdata σ _ _ at h₂
  rw [hoff] at h₂
  exact ⟨_, _, h₂⟩

theorem safeExecDecodeFinish {I g s0 σ k C aw mem rdata len} {ptr ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨12716⟩
      (ptr :: execDecodeSignaturesSaved I.calldata len ret R) mem aw rdata σ k C)
    (hov : R.length + 26 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (execTransactionDecodedStack I.calldata len ptr R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_12716 (by change R.length + 16 ≤ 1024; omega) hret h
  exact ⟨_, _, h₁⟩

end Benchmarks.Safe.Runs1e6
