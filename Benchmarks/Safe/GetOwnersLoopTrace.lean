import Benchmarks.Safe.GetOwnersMemory
import Benchmarks.Safe.OwnerStorage
import Benchmarks.Safe.CheckedIncrement
import Benchmarks.Safe.Blocks.Runtime_023
import Benchmarks.Safe.Blocks.Runtime_050

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeGetOwnersLoopExit {I g s0 σ k C aw mem rdata i ret} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4419⟩
      (⟨1⟩ :: UInt256.ofNat i :: ⟨128⟩ :: ⟨96⟩ :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (⟨128⟩ :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_4419_taken (by simp; omega) (by decide) (by jump_dest) h
  have h₂ := safeRuntime_block_4516 (by omega) hret h₁
  exact ⟨_, _, h₂⟩

set_option maxHeartbeats 800000 in
theorem safeGetOwnersLoopNext {I g s0 σ k C aw mem rdata n words i current}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4419⟩
      (current :: UInt256.ofNat i :: ⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hn : n ≤ 2 ^ 64 - 1) (hi : i < n)
    (hc : current.toNat < EVM.addressModulus) (hs : current ≠ ⟨1⟩) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨4419⟩
      (ownerLinkAt σ I current :: UInt256.ofNat (i + 1) :: ⟨128⟩ :: R)
      (getOwnersStepMemory mem i current) aw' rdata σ k' C' := by
  have hiword := ulit_toNat' i (by change i < 2 ^ 256; omega)
  have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
  have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat n :=
    mloadWordValue_of_readWithPadding (by change 128 < mem.size; have := hm.lower; omega)
      hm.count
  have h₁ := safeRuntime_block_4419_fallthrough (by simp; omega)
    (by simpa only [safeAddressMask, solcAddrMask_clean hc] using
      (u256_eq_of_ne (Ne.symm hs))) h
  have hlt := ult_one (a := UInt256.ofNat i) (b := UInt256.ofNat n)
    (by simpa only [hiword, hnword] using hi)
  have h₂ := safeRuntime_block_4437_taken (by omega)
    (by rw [hcount, hlt]; decide) (by jump_dest) h₁
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_4455_packed
    (by simp only [safeRuntime_block_4437_taken_stack, List.length_cons]; omega)
    (by jump_dest) h₂
  have hp := safeAddressArrayIndexAddress i (by omega)
  simp only [safeRuntime_block_4437_taken_stack, safeRuntime_block_4455_stack,
    safeRuntime_block_4455_memory, safeAddressMask, solcAddrMask_clean_left hc] at h₃
  change (UInt256.ofNat 32 + (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i) +
    (⟨128⟩ : UInt256))).toNat = 160 + 32 * i at hp
  rw [hp] at h₃
  have hh := twoWordHashMem_mapSlot_of_ge64 (mem := writeWord mem (160 + 32 * i) current)
    current ⟨2⟩ (by rw [writeWord_sparse_size]; have := hm.lower; omega)
  change keccakWord ⟨0⟩ ⟨64⟩ (getOwnersStepMemory mem i current) = mapSlot current ⟨2⟩ at hh
  change RD safeBytecode I g s0 ⟨11161⟩
    (UInt256.ofNat i :: ⟨4509⟩ ::
      UInt256.land (solcSlotWordAt
        (keccakWord ⟨0⟩ ⟨64⟩ (getOwnersStepMemory mem i current)) σ I) solcAddrMask ::
      UInt256.ofNat i :: ⟨128⟩ :: R)
    (getOwnersStepMemory mem i current) aw₃ rdata σ k₃ C₃ at h₃
  rw [hh] at h₃
  obtain ⟨k₄, C₄, h₄⟩ := safeIncrementTrace h₃ (by simp; omega)
    (by rw [hiword]; change i + 1 < 2 ^ 256; omega) (by jump_dest)
  have hinc : UInt256.ofNat i + (⟨1⟩ : UInt256) = UInt256.ofNat (i + 1) := by
    apply u256_inj
    rw [uadd_toNat, hiword]
    rfl
  have h₅ := safeRuntime_block_4509 (by simp; omega) (by jump_dest) h₄
  simpa only [safeRuntime_block_4509_stack, hinc, ownerLinkAt] using
    (show ∃ aw' k' C', RD safeBytecode I g s0 ⟨4419⟩ _ _ aw' rdata σ k' C' from
      ⟨_, _, _, h₅⟩)

theorem safeGetOwnersLoopOutOfBounds {I g s0 σ k C aw mem rdata n words i current}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4419⟩
      (current :: UInt256.ofNat i :: ⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hi : i = n) (hc : current.toNat < EVM.addressModulus) (hs : current ≠ ⟨1⟩) :
    RDrev safeBytecode g s0 := by
  have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat n :=
    mloadWordValue_of_readWithPadding (by change 128 < mem.size; have := hm.lower; omega)
      hm.count
  have h₁ := safeRuntime_block_4419_fallthrough (by simp; omega)
    (by simpa only [safeAddressMask, solcAddrMask_clean hc] using
      (u256_eq_of_ne (Ne.symm hs))) h
  have h₂ := safeRuntime_block_4437_fallthrough (by omega)
    (by rw [hcount, hi]; exact ult_zero (by omega)) h₁
  have h₃ := safeRuntime_block_4448
    (by simp only [safeRuntime_block_4437_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₂
  exact safeRuntime_block_11505
    (by simp only [safeRuntime_block_4437_fallthrough_stack,
      safeRuntime_block_4448_stack, List.length_cons]; omega) h₃

end Benchmarks.Safe
