import Benchmarks.Safe.SetupDecodeOwners
import Benchmarks.Safe.AddressCalldataRead
import Benchmarks.Safe.Blocks.Runtime_047

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

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
    (h : RD safeBytecode I g s0 ⟨10503⟩ (setupDecodeOwnersStack I.calldata n ret R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 4).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9096⟩
      (⟨68⟩ :: ⟨10529⟩ :: setupDecodeTargetSaved I.calldata n ret R) mem aw rdata σ k' C' := by
  have hptr : UInt256.ofNat 32 + UInt256.ofNat (4 + (calldataWord I.calldata 4).toNat) =
      UInt256.ofNat (setupOwnersStart I.calldata) := by
    rw [wordOfNatAdd _ _ (by change _ < 2 ^ 256; omega)]
    congr 1
    dsimp only [setupOwnersStart]
    omega
  have h₁ := safeRuntime_block_10503 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_10503_stack, hptr,
    show (⟨4⟩ : UInt256) + UInt256.ofNat 64 = ⟨68⟩ by decide +kernel,
    show ((⟨4⟩ : UInt256) + UInt256.ofNat 32).toNat = 36 by decide +kernel] at h₁
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeDataStart {I g s0 σ k C aw mem rdata n} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10529⟩
      (calldataWord I.calldata 68 :: setupDecodeTargetSaved I.calldata n ret R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 100).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9154⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 100).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨10567⟩ :: setupDecodeDataSaved I.calldata n ret R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_10529_taken (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 100) _) ≠ _
    rw [hmax, ugt_zero ho]; decide) (by jump_dest) h
  change RD safeBytecode I g s0 ⟨10555⟩ (setupDecodeDataSaved I.calldata n ret R)
    mem aw rdata σ _ _ at h₁
  have h₂ := safeRuntime_block_10555 (by simp; omega) (by jump_dest) h₁
  have hoff : (⟨4⟩ : UInt256) + calldataWord I.calldata 100 =
      UInt256.ofNat (4 + (calldataWord I.calldata 100).toNat) := by
    simpa only [u256_ofNat_toNat] using
      wordOfNatAdd 4 (calldataWord I.calldata 100).toNat (by change _ < 2 ^ 256; omega)
  simp only [safeRuntime_block_10555_stack] at h₂
  rw [hoff] at h₂
  exact ⟨_, _, h₂⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeDataOffsetRevert {I g s0 σ k C aw mem rdata n} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10529⟩
      (calldataWord I.calldata 68 :: setupDecodeTargetSaved I.calldata n ret R)
      mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 100).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 22 ≤ 1024) : RDrev safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_10529_fallthrough (by simp; omega) (by
    change UInt256.isZero (UInt256.gt (calldataWord I.calldata 100) _) = _
    rw [hmax, ugt_one (by exact Nat.lt_of_not_ge ho)]; decide) h
  exact safeRuntime_block_10552 (by change R.length + 16 ≤ 1024; omega) h₁

set_option maxRecDepth 100000 in
theorem safeSetupDecodeFallbackStart {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10567⟩
      (UInt256.ofNat len :: UInt256.ofNat (setupDataStart I.calldata) ::
        setupDecodeDataSaved I.calldata n ret R) mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9096⟩
      (⟨132⟩ :: ⟨10586⟩ :: setupDecodeFallbackSaved I.calldata n len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10567 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeTokenStart {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10586⟩
      (calldataWord I.calldata 132 :: setupDecodeFallbackSaved I.calldata n len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9096⟩
      (⟨164⟩ :: ⟨10600⟩ :: setupDecodeTokenSaved I.calldata n len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10586 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeReceiverStart {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10600⟩
      (calldataWord I.calldata 164 :: setupDecodeTokenSaved I.calldata n len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨9096⟩
      (⟨228⟩ :: ⟨10621⟩ :: setupDecodeReceiverSaved I.calldata n len ret R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10600 (by simp; omega) (by jump_dest) h
  exact ⟨_, _, h₁⟩

set_option maxRecDepth 100000 in
theorem safeSetupDecodeFinish {I g s0 σ k C aw mem rdata n len} {ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨10621⟩
      (calldataWord I.calldata 228 :: setupDecodeReceiverSaved I.calldata n len ret R)
      mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_10621 (by simp; omega) hret h
  exact ⟨_, _, h₁⟩

end Benchmarks.Safe
