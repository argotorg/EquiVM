import Benchmarks.Safe.ViaIR.GetOwnersMemory
import Benchmarks.Safe.ViaIR.OwnerStorage
import Benchmarks.Safe.ViaIR.CheckedIncrement
import Benchmarks.Safe.ViaIR.Blocks.Runtime_019
import Benchmarks.Safe.ViaIR.Blocks.Runtime_020
import Benchmarks.Safe.ViaIR.Blocks.Runtime_042

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeGetOwnersLoopExit {I g s0 σ k C aw mem rdata i} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4105⟩
      (⟨1⟩ :: ⟨0⟩ :: UInt256.ofNat i :: ⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨4171⟩
      (⟨1⟩ :: ⟨0⟩ :: UInt256.ofNat i :: ⟨128⟩ :: R) mem aw rdata σ k' C' := by
  have hout := safeRuntime_block_4105_taken (by simp; omega) (by decide) (by jump_dest) h
  exact ⟨_, _, hout⟩

set_option maxHeartbeats 800000 in
theorem safeGetOwnersLoopNext {I g s0 σ k C aw mem rdata n words i current}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4105⟩
      (current :: ⟨0⟩ :: UInt256.ofNat i :: ⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hn : n ≤ 2 ^ 64 - 1) (hi : i < n)
    (hc : current.toNat < EVM.addressModulus) (hs : current ≠ ⟨1⟩) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨4105⟩
      (ownerLinkAt σ I current :: ⟨0⟩ :: UInt256.ofNat (i + 1) :: ⟨128⟩ :: R)
      (getOwnersStepMemory mem i current) aw' rdata σ k' C' := by
  have hiword := ulit_toNat' i (by change i < 2 ^ 256; omega)
  have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
  have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat n :=
    mloadWordValue_of_readWithPadding (by change 128 < mem.size; have := hm.lower; omega)
      hm.count
  have h4123 := safeRuntime_block_4105_fallthrough (by simp; omega)
    (by simpa only [safeAddressMask, solcAddrMask_clean_left hc] using u256_eq_of_ne hs) h
  simp only [safeRuntime_block_4105_fallthrough_stack, safeAddressMask,
    solcAddrMask_clean_left hc] at h4123
  have h9000 := safeRuntime_block_4123 (by omega) (by jump_dest) h4123
  simp only [safeRuntime_block_4123_stack] at h9000
  have hlt := ult_one (a := UInt256.ofNat i) (b := UInt256.ofNat n)
    (by simpa only [hiword, hnword] using hi)
  have h9010 := safeRuntime_block_9000_fallthrough (by simp; omega)
    (by rw [hcount, hlt]; decide) h9000
  have h4133 := safeRuntime_block_9010 (by simp; omega) (by jump_dest) h9010
  simp only [safeRuntime_block_9010_stack] at h4133
  obtain ⟨aw', k', C', h7497⟩ := safeRuntime_block_4133_packed
    (by simp; omega) (by jump_dest) h4133
  have hp : ((UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + (⟨128⟩ : UInt256)) +
      UInt256.ofNat 32).toNat = 160 + 32 * i := by
    change ((UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) + UInt256.ofNat 128) +
      UInt256.ofNat 32).toNat = _
    have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
        UInt256.ofNat (32 * i) := shiftLeft5_ofNat_eq (by change 32 * i < 2 ^ 256; omega)
    rw [hshift, uadd3_ofNat_toNat (by change 32 * i < 2 ^ 256; omega) (by decide)
      (by decide) (by change 32 * i + 128 < 2 ^ 256; omega)
      (by change 32 * i + 128 + 32 < 2 ^ 256; omega)]
    omega
  simp only [safeRuntime_block_4133_stack, safeRuntime_block_4133_memory,
    safeAddressMask, hp] at h7497
  have hh := twoWordHashMem_mapSlot_of_ge64 (mem := writeWord mem (160 + 32 * i) current)
    current ⟨2⟩ (by rw [writeWord_sparse_size]; have := hm.lower; omega)
  change keccakWord ⟨0⟩ ⟨64⟩ (getOwnersStepMemory mem i current) = mapSlot current ⟨2⟩ at hh
  change RD fork safeBytecode I g s0 ⟨7497⟩
    (UInt256.ofNat i :: ⟨4165⟩ :: ⟨0⟩ ::
      UInt256.land solcAddrMask (solcSlotWordAt
        (keccakWord ⟨0⟩ ⟨64⟩ (getOwnersStepMemory mem i current)) σ I) :: ⟨128⟩ :: R)
    (getOwnersStepMemory mem i current) aw' rdata σ k' C' at h7497
  rw [hh, u256_land_comm solcAddrMask _] at h7497
  obtain ⟨_, _, h4165⟩ := safeIncrementTrace h7497 (by simp; omega)
    (by rw [hiword]; change i + 1 < 2 ^ 256; omega) (by jump_dest)
  have hinc : UInt256.ofNat i + (⟨1⟩ : UInt256) = UInt256.ofNat (i + 1) := by
    apply u256_inj
    rw [uadd_toNat, hiword]
    rfl
  have hout := safeRuntime_block_4165 (by simp; omega) (by jump_dest) h4165
  simp only [safeRuntime_block_4165_stack, hinc] at hout
  exact ⟨_, _, _, hout⟩

theorem safeGetOwnersLoopOutOfBounds {I g s0 σ k C aw mem rdata n words i current}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4105⟩
      (current :: ⟨0⟩ :: UInt256.ofNat i :: ⟨128⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hi : i = n) (hc : current.toNat < EVM.addressModulus) (hs : current ≠ ⟨1⟩) :
    RDrev fork safeBytecode g s0 := by
  have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat n :=
    mloadWordValue_of_readWithPadding (by change 128 < mem.size; have := hm.lower; omega)
      hm.count
  have h4123 := safeRuntime_block_4105_fallthrough (by simp; omega)
    (by simpa only [safeAddressMask, solcAddrMask_clean_left hc] using u256_eq_of_ne hs) h
  simp only [safeRuntime_block_4105_fallthrough_stack, safeAddressMask,
    solcAddrMask_clean_left hc] at h4123
  have h9000 := safeRuntime_block_4123 (by omega) (by jump_dest) h4123
  simp only [safeRuntime_block_4123_stack] at h9000
  have h9020 := safeRuntime_block_9000_taken (by simp; omega)
    (by rw [hcount, hi, ult_zero (by omega)]; decide) (by jump_dest) h9000
  exact safeRuntime_block_9020 (by simp; omega) h9020

end Benchmarks.Safe.ViaIR
