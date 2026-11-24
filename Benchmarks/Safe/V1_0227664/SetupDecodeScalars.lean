import Benchmarks.Safe.V1_0227664.SetupDecodeOwners
import Benchmarks.Safe.V1_0227664.AddressCalldataRead
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_045

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

def setupDecodeTargetSaved (cd : ByteArray) (n : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, calldataWord cd 36,
    UInt256.ofNat n, UInt256.ofNat (setupOwnersStart cd), ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def setupDecodeDataSaved (cd : ByteArray) (n : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [calldataWord cd 100, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩,
    calldataWord cd 68, calldataWord cd 36, UInt256.ofNat n, UInt256.ofNat (setupOwnersStart cd),
    ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def setupDecodeFallbackSaved (cd : ByteArray) (n len : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, ⟨0⟩, ⟨0⟩, UInt256.ofNat len, UInt256.ofNat (setupDataStart cd),
    calldataWord cd 68, calldataWord cd 36, UInt256.ofNat n, UInt256.ofNat (setupOwnersStart cd),
    ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def setupDecodeTokenSaved (cd : ByteArray) (n len : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [⟨0⟩, ⟨0⟩, ⟨0⟩, calldataWord cd 132, UInt256.ofNat len, UInt256.ofNat (setupDataStart cd),
    calldataWord cd 68, calldataWord cd 36, UInt256.ofNat n, UInt256.ofNat (setupOwnersStart cd),
    ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def setupDecodeReceiverSaved (cd : ByteArray) (n len : Nat) (ret : UInt256)
    (R : List UInt256) : List UInt256 :=
  [⟨0⟩, calldataWord cd 196, calldataWord cd 164, calldataWord cd 132,
    UInt256.ofNat len, UInt256.ofNat (setupDataStart cd), calldataWord cd 68, calldataWord cd 36,
    UInt256.ofNat n, UInt256.ofNat (setupOwnersStart cd), ⟨4⟩, UInt256.ofNat cd.size, ret] ++ R

def setupDecodedStack (cd : ByteArray) (n len : Nat) (R : List UInt256) : List UInt256 :=
  [calldataWord cd 228, calldataWord cd 196, calldataWord cd 164, calldataWord cd 132,
    UInt256.ofNat len, UInt256.ofNat (setupDataStart cd), calldataWord cd 68, calldataWord cd 36,
    UInt256.ofNat n, UInt256.ofNat (setupOwnersStart cd)] ++ R

set_option maxRecDepth 100000 in
theorem safeSetupDecodeTargetStart {I g s0 σ k C aw mem rdata n} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10116⟩ (setupDecodeOwnersStack I.calldata n ret R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8719⟩
      (⟨68⟩ :: ⟨10142⟩ :: setupDecodeTargetSaved I.calldata n ret R) mem aw rdata σ k' C' := by
  have hptr : UInt256.ofNat 32 + UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat) =
      UInt256.ofNat (setupOwnersStart I.calldata) := by
    rw [wordOfNatAdd _ _ (by change _ < 2 ^ 256; omega)]
    congr 1
    dsimp only [setupOwnersStart]
    omega
  have h₁ := safeRuntime_block_10116 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_10116_stack, hptr,
    show (⟨4⟩ : UInt256) + UInt256.ofNat 64 = ⟨68⟩ by decide +kernel,
    show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₁
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeDataStart {I g s0 σ k C aw mem rdata n} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10142⟩
      (calldataWord I.calldata 68 :: setupDecodeTargetSaved I.calldata n ret R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 100).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8777⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 100).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨10180⟩ :: setupDecodeDataSaved I.calldata n ret R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_10142_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 100) _) ≠ _
    rw [hmax, ugt_zero ho]; decide) (by jump_dest) h
  change RD fork safeBytecode I g s0 ⟨10168⟩ (setupDecodeDataSaved I.calldata n ret R)
    mem aw rdata σ _ _ at h₁
  have h₂ := safeRuntime_block_10168 (by simp; omega) (by jump_dest) h₁
  have hoff : (⟨4⟩ : UInt256) + calldataWord I.calldata 100 =
      UInt256.ofNat (4 + (calldataWord I.calldata 100).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 100).toNat (by change _ < 2 ^ 256; omega)
  simp only [safeRuntime_block_10168_stack] at h₂
  rw [hoff] at h₂
  exact ⟨_, _, h₂⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeDataOffsetRevert {I g s0 σ k C aw mem rdata n} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10142⟩
      (calldataWord I.calldata 68 :: setupDecodeTargetSaved I.calldata n ret R)
      mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 100).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 22 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_10142_fallthrough (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 100) _) = _
    rw [hmax, ugt_one (by exact Nat.lt_of_not_ge ho)]; decide) h
  exact safeRuntime_block_10165 (by change R.length + 16 ≤ 1024; omega) h₁

set_option maxRecDepth 100000 in
theorem safeSetupDecodeFallbackStart {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10180⟩
      (UInt256.ofNat len :: UInt256.ofNat (setupDataStart I.calldata) ::
        setupDecodeDataSaved I.calldata n ret R) mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8719⟩
      (⟨132⟩ :: ⟨10199⟩ :: setupDecodeFallbackSaved I.calldata n len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10180 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeTokenStart {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10199⟩
      (calldataWord I.calldata 132 :: setupDecodeFallbackSaved I.calldata n len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8719⟩
      (⟨164⟩ :: ⟨10213⟩ :: setupDecodeTokenSaved I.calldata n len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10199 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeReceiverStart {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10213⟩
      (calldataWord I.calldata 164 :: setupDecodeTokenSaved I.calldata n len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨8719⟩
      (⟨228⟩ :: ⟨10234⟩ :: setupDecodeReceiverSaved I.calldata n len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10213 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeFinish {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨10234⟩
      (calldataWord I.calldata 228 :: setupDecodeReceiverSaved I.calldata n len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10234 (by simp; omega) hret h
  exact ⟨_, _, h₁⟩

end Benchmarks.Safe.V1_0227664
