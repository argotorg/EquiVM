import Benchmarks.Safe.ViaIR.SetupDecodeOwners
import Benchmarks.Safe.ViaIR.Decoders

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

def setupDecodeTargetSaved (cd : ByteArray) (n : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat (setupOwnersStart cd), UInt256.ofNat (setupOwnersStart cd + 32 * n),
    calldataWord cd 36, UInt256.ofNat n, ⟨0⟩] ++ R

def setupDecodeDataSaved (cd : ByteArray) (n : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat (setupOwnersStart cd), calldataWord cd 68,
    UInt256.ofNat (setupOwnersStart cd + 32 * n), calldataWord cd 36, UInt256.ofNat n, ⟨0⟩] ++ R

def setupDecodeFallbackSaved (cd : ByteArray) (n len : Nat) (R : List UInt256) : List UInt256 :=
  [UInt256.ofNat len, UInt256.ofNat (setupDataStart cd)] ++ setupDecodeDataSaved cd n R

def setupDecodeTokenSaved (cd : ByteArray) (n len : Nat) (R : List UInt256) : List UInt256 :=
  [calldataWord cd 132, UInt256.ofNat len, UInt256.ofNat (setupDataStart cd),
    calldataWord cd 68, UInt256.ofNat (setupOwnersStart cd), calldataWord cd 132,
    UInt256.ofNat (setupOwnersStart cd + 32 * n), calldataWord cd 36, UInt256.ofNat n, ⟨0⟩] ++ R

def setupDecodeReceiverSaved (cd : ByteArray) (n len : Nat) (R : List UInt256) : List UInt256 :=
  [calldataWord cd 132, calldataWord cd 132, UInt256.ofNat len,
    UInt256.ofNat (setupDataStart cd), calldataWord cd 68, UInt256.ofNat (setupOwnersStart cd),
    calldataWord cd 164, UInt256.ofNat (setupOwnersStart cd + 32 * n), calldataWord cd 36,
    UInt256.ofNat n, ⟨0⟩] ++ R

def setupDecodedStack (cd : ByteArray) (n len : Nat) (R : List UInt256) : List UInt256 :=
  [calldataWord cd 228, UInt256.ofNat (setupOwnersStart cd + 32 * n), calldataWord cd 36,
    calldataWord cd 132, calldataWord cd 132, UInt256.ofNat len,
    UInt256.ofNat (setupDataStart cd), calldataWord cd 68, ⟨0⟩, calldataWord cd 164,
    UInt256.ofNat (setupOwnersStart cd), calldataWord cd 196, UInt256.ofNat n, ⟨0⟩] ++ R

set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

theorem safeSetupDecodeTargetStart {I g s0 σ k C aw mem rdata n} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3060⟩ (setupDecodeOwnersStack I.calldata n (⟨0⟩ :: R))
      mem aw rdata σ k C)
    (hc : (calldataWord I.calldata 68).toNat < EVM.addressModulus)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨3071⟩
      (calldataWord I.calldata 68 :: setupDecodeTargetSaved I.calldata n R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_3060 (by simp; omega) (by jump_dest) h
  have h₂ := safeRuntime_block_6996_fallthrough (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 68)
      (UInt256.land (calldataWord I.calldata 68) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hc]; exact u256_sub_self _) h₁
  exact ⟨_, _, safeRuntime_block_7017 (by simp [setupDecodeTargetSaved]; omega)
    (by jump_dest) h₂⟩

theorem safeSetupDecodeTargetRevert {I g s0 σ k C aw mem rdata n} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3060⟩ (setupDecodeOwnersStack I.calldata n (⟨0⟩ :: R))
      mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata 68).toNat < EVM.addressModulus)
    (hov : R.length + 22 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_3060 (by simp; omega) (by jump_dest) h
  have h₂ := safeRuntime_block_6996_taken (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 68)
      (UInt256.land (calldataWord I.calldata 68) solcAddrMask) ≠ ⟨0⟩
    intro heq
    exact hc (u256_sub_eq_zero_iff_eq.mp heq ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h₁
  exact safeRuntime_block_111 (by
    simp [safeRuntime_block_6996_taken_stack]; omega) h₂

theorem safeSetupDecodeDataStart {I g s0 σ k C aw mem rdata n} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3071⟩
      (calldataWord I.calldata 68 :: setupDecodeTargetSaved I.calldata n R)
      mem aw rdata σ k C)
    (ho : (calldataWord I.calldata 100).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨7083⟩
      (UInt256.ofNat (4 + (calldataWord I.calldata 100).toNat) ::
        UInt256.ofNat I.calldata.size :: ⟨3103⟩ :: setupDecodeDataSaved I.calldata n R)
      mem aw rdata σ k' C' := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_3071_fallthrough (by simp; omega) (by
    rw [hmax]
    change UInt256.gt (calldataWord I.calldata 100) _ = _
    exact ugt_zero (by simpa only [show (UInt256.ofNat (2 ^ 64 - 1)).toNat =
      2 ^ 64 - 1 from by decide +kernel] using ho)) h
  have h₂ := safeRuntime_block_3090 (by simp; omega) (by jump_dest) h₁
  have hoff : (UInt256.ofNat 4) + calldataWord I.calldata 100 =
      UInt256.ofNat (4 + (calldataWord I.calldata 100).toNat) := by
    conv_lhs => rhs; rw [← u256_ofNat_toNat (calldataWord I.calldata 100)]
    exact wordOfNatAdd _ _ (by change _ < 2 ^ 256; omega)
  simp only [safeRuntime_block_3090_stack, hoff] at h₂
  exact ⟨_, _, h₂⟩

theorem safeSetupDecodeDataOffsetRevert {I g s0 σ k C aw mem rdata n} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3071⟩
      (calldataWord I.calldata 68 :: setupDecodeTargetSaved I.calldata n R)
      mem aw rdata σ k C)
    (ho : ¬(calldataWord I.calldata 100).toNat ≤ 2 ^ 64 - 1)
    (hov : R.length + 22 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have hmax : UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
      (UInt256.ofNat 1) = UInt256.ofNat (2 ^ 64 - 1) := by decide +kernel
  have h₁ := safeRuntime_block_3071_taken (by simp; omega) (by
    rw [hmax]
    change UInt256.gt (calldataWord I.calldata 100) _ ≠ _
    rw [ugt_one (by
      rw [show (UInt256.ofNat (2 ^ 64 - 1)).toNat = 2 ^ 64 - 1 by decide +kernel]
      omega)]; decide) (by jump_dest) h
  exact safeRuntime_block_3905 (by simp; omega) h₁

theorem safeSetupDecodeFallbackStart {I g s0 σ k C aw mem rdata n len}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3103⟩ (setupDecodeFallbackSaved I.calldata n len R)
      mem aw rdata σ k C)
    (hc : (calldataWord I.calldata 132).toNat < EVM.addressModulus)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨3128⟩ (setupDecodeTokenSaved I.calldata n len R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_3103_fallthrough (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 132)
      (UInt256.land (calldataWord I.calldata 132) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hc]; exact u256_sub_self _) h
  simp only [safeRuntime_block_3103_fallthrough_stack, safeAddressMask] at h₁
  change RD fork safeBytecode I g s0 ⟨3128⟩
    (calldataWord I.calldata 132 :: UInt256.ofNat len :: UInt256.ofNat (setupDataStart I.calldata) ::
      calldataWord I.calldata 68 :: UInt256.ofNat (setupOwnersStart I.calldata) ::
      UInt256.land (calldataWord I.calldata 132) solcAddrMask ::
      UInt256.ofNat (setupOwnersStart I.calldata + 32 * n) :: calldataWord I.calldata 36 ::
      UInt256.ofNat n :: ⟨0⟩ :: R) mem aw rdata σ _ _ at h₁
  rw [solcAddrMask_clean hc] at h₁
  exact ⟨_, _, h₁⟩

theorem safeSetupDecodeFallbackRevert {I g s0 σ k C aw mem rdata n len}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3103⟩ (setupDecodeFallbackSaved I.calldata n len R)
      mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata 132).toNat < EVM.addressModulus)
    (hov : R.length + 22 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_3103_taken (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 132)
      (UInt256.land (calldataWord I.calldata 132) solcAddrMask) ≠ ⟨0⟩
    intro heq
    exact hc (u256_sub_eq_zero_iff_eq.mp heq ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_3901 (by simp; omega) h₁

theorem safeSetupDecodeTokenStart {I g s0 σ k C aw mem rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3128⟩ (setupDecodeTokenSaved I.calldata n len R)
      mem aw rdata σ k C)
    (hc : (calldataWord I.calldata 164).toNat < EVM.addressModulus)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨3148⟩ (setupDecodeReceiverSaved I.calldata n len R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_3128_fallthrough (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 164)
      (UInt256.land (calldataWord I.calldata 164) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hc]; exact u256_sub_self _) h
  exact ⟨_, _, h₁⟩

theorem safeSetupDecodeTokenRevert {I g s0 σ k C aw mem rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3128⟩ (setupDecodeTokenSaved I.calldata n len R)
      mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata 164).toNat < EVM.addressModulus)
    (hov : R.length + 22 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_3128_taken (by simp; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 164)
      (UInt256.land (calldataWord I.calldata 164) solcAddrMask) ≠ ⟨0⟩
    intro heq
    exact hc (u256_sub_eq_zero_iff_eq.mp heq ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_3897 (by simp; omega) h₁

theorem safeSetupDecodeReceiverStart {I g s0 σ k C aw mem rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3148⟩ (setupDecodeReceiverSaved I.calldata n len R)
      mem aw rdata σ k C)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6974⟩
      (⟨3163⟩ :: (setupDecodedStack I.calldata n len R).tail) mem aw rdata σ k' C' := by
  exact ⟨_, _, safeRuntime_block_3148 (by simp; omega) (by jump_dest) h⟩

theorem safeSetupDecodeFinish {I g s0 σ k C aw mem rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6974⟩
      (⟨3163⟩ :: (setupDecodedStack I.calldata n len R).tail) mem aw rdata σ k C)
    (hc : (calldataWord I.calldata 228).toNat < EVM.addressModulus)
    (hov : R.length + 22 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨3163⟩ (setupDecodedStack I.calldata n len R)
      mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_6974_fallthrough (by simp [setupDecodedStack]; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 228)
      (UInt256.land (calldataWord I.calldata 228) solcAddrMask) = ⟨0⟩
    rw [solcAddrMask_clean hc]; exact u256_sub_self _) h
  exact ⟨_, _, safeRuntime_block_6995 (by simp [setupDecodedStack]; omega) (by jump_dest) h₁⟩

theorem safeSetupDecodeReceiverRevert {I g s0 σ k C aw mem rdata n len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6974⟩
      (⟨3163⟩ :: (setupDecodedStack I.calldata n len R).tail) mem aw rdata σ k C)
    (hc : ¬(calldataWord I.calldata 228).toNat < EVM.addressModulus)
    (hov : R.length + 22 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6974_taken (by simp [setupDecodedStack]; omega) (by
    rw [safeAddressMask]
    change UInt256.sub (calldataWord I.calldata 228)
      (UInt256.land (calldataWord I.calldata 228) solcAddrMask) ≠ ⟨0⟩
    intro heq
    exact hc (u256_sub_eq_zero_iff_eq.mp heq ▸ solcAddrMask_result_canonical _))
    (by jump_dest) h
  exact safeRuntime_block_111 (by
    simp [safeRuntime_block_6974_taken_stack, setupDecodedStack]; omega) h₁

end Benchmarks.Safe.ViaIR
