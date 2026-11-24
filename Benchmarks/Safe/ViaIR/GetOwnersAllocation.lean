import Benchmarks.Safe.ViaIR.GetOwnersMemory
import Benchmarks.Safe.ViaIR.OwnerStorage
import Benchmarks.Safe.ViaIR.Memory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_019
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034
import Benchmarks.Safe.ViaIR.Blocks.Runtime_041
import Benchmarks.Safe.ViaIR.Blocks.Runtime_042

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

def getOwnersAllocatedMemory (n : Nat) : ByteArray :=
  writeWord (writeWord solcFreePtrMem 64 (addressArrayFreePtr n)) 128 (UInt256.ofNat n)

theorem getOwnersAllocatedMemory_size (n : Nat) :
    (getOwnersAllocatedMemory n).size = 160 := by
  simp only [getOwnersAllocatedMemory, writeWord_sparse_size, solcFreePtrMem_size]
  decide +kernel

theorem safeGetOwnersAllocated (n : Nat) :
    AddressArrayMemory (getOwnersAllocatedMemory n) n (List.replicate n ⟨0⟩) := by
  have hs := getOwnersAllocatedMemory_size n
  have hm : (writeWord solcFreePtrMem 64 (addressArrayFreePtr n)).size = 96 := by
    simp only [writeWord_sparse_size, solcFreePtrMem_size]
    decide
  refine ⟨List.length_replicate, by rw [hs], by omega, by omega, ?_, ?_, ?_⟩
  · rw [getOwnersAllocatedMemory,
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by decide, by rw [hm]⟩)]
    exact writeWord_sparse_read_back _ _ _
  · exact writeWord_sparse_read_back _ _ _
  · exact WordArrayMemory.zeroes _ _ _ (by omega)

theorem safeGetOwnersFinalPointer (n : Nat) (hn : n ≤ 2 ^ 64 - 1) :
    UInt256.ofNat 128 + UInt256.land
      ((UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5)) +
        UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31)) = addressArrayFreePtr n := by
  have hshift : UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5) =
      UInt256.ofNat (32 * n) := shiftLeft5_ofNat_eq (by change 32 * n < 2 ^ 256; omega)
  have halloc : UInt256.ofNat 32 + UInt256.ofNat (32 * n) =
      UInt256.ofNat (32 * n + 32) := u256_32_add_ofNat _
  rw [hshift, halloc, u256_land_comm,
    u256_add_comm (UInt256.ofNat (32 * n + 32)),
    wordAlignedRoundUp (32 * n + 32)
      (by change 32 * n + 32 + 31 < 2 ^ 256; omega) (by omega)]
  apply u256_inj
  change (UInt256.add (UInt256.ofNat 128) (UInt256.ofNat (32 * n + 32))).toNat = _
  rw [uadd_ofNat_toNat (by decide) (by change 32 * n + 32 < 2 ^ 256; omega)
    (by change 128 + (32 * n + 32) < 2 ^ 256; omega), addressArrayFreePtr,
    ulit_toNat' _ (by change 160 + 32 * n < 2 ^ 256; omega)]
  omega

theorem safeGetOwnersAllocationMemory (n : Nat) :
    safeRuntime_block_8973_memory
      (mem := safeRuntime_block_7157_memory (mem := solcFreePtrMem)
        (x0 := addressArrayFreePtr n)) (x0 := UInt256.ofNat 128) (x2 := UInt256.ofNat n) =
      getOwnersAllocatedMemory n := by rfl

theorem safeGetOwnersCountCheck {I g s0 σ k C aw mem rdata count ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8927⟩ (count :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hn : count.toNat ≤ 2 ^ 64 - 1)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret
      ((UInt256.ofNat 32 + UInt256.shiftLeft count (UInt256.ofNat 5)) :: R)
      mem aw rdata σ k' C' := by
  have h8942 := safeRuntime_block_8927_fallthrough (by simp; omega) (ugt_zero hn) h
  have hout := safeRuntime_block_8942 (by omega) hret h8942
  exact ⟨_, _, hout⟩

set_option maxHeartbeats 800000 in
theorem safeGetOwnersAllocate {I g s0 σ k C aw rdata n} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8950⟩
      (UInt256.ofNat n :: ⟨4076⟩ :: ⟨0⟩ :: R) solcFreePtrMem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hn : n ≤ 2 ^ 59 - 6)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨4105⟩
      (ownerLinkAt σ I ⟨1⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: R)
      (twoWordHashMem ⟨1⟩ ⟨2⟩ (getOwnersAllocatedMemory n)) aw' rdata σ k' C' := by
  have hb : n ≤ 2 ^ 64 - 1 := by omega
  have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
  have hp := safeGetOwnersFinalPointer n hb
  have h8927 := safeRuntime_block_8950 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_8950_stack] at h8927
  obtain ⟨_, _, h8960⟩ := safeGetOwnersCountCheck h8927 (by simp; omega)
    (by rwa [hnword]) (by jump_dest)
  obtain ⟨_, _, _, h7128⟩ := safeRuntime_block_8960_packed (by simp; omega) (by jump_dest) h8960
  simp only [safeRuntime_block_8960_stack] at h7128
  rw [show memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 from
    solcFreePtrMem_mload64] at h7128
  have hfp := ulit_toNat' (160 + 32 * n) (by change 160 + 32 * n < 2 ^ 256; omega)
  have h7157 := safeRuntime_block_7128_fallthrough (by simp; omega) (by
    rw [hp]
    rw [ugt_zero (by
      change (addressArrayFreePtr n).toNat ≤ 2 ^ 64 - 1
      rw [addressArrayFreePtr, hfp]; omega), ult_zero (by
      change 128 ≤ (addressArrayFreePtr n).toNat
      rw [addressArrayFreePtr, hfp]; omega), u256_lor_zero]
    rfl) h7128
  simp only [safeRuntime_block_7128_fallthrough_stack, hp] at h7157
  obtain ⟨_, _, _, h8973⟩ := safeRuntime_block_7157_packed (by simp; omega) (by jump_dest) h7157
  simp only [safeRuntime_block_7157_stack] at h8973
  obtain ⟨_, _, _, hcount⟩ := safeRuntime_block_8973_packed (by simp; omega) (by jump_dest) h8973
  simp only [safeRuntime_block_8973_stack, safeGetOwnersAllocationMemory] at hcount
  obtain ⟨_, _, h8990⟩ := safeGetOwnersCountCheck hcount (by simp; omega)
    (by rwa [hnword]) (by jump_dest)
  obtain ⟨_, _, _, h4076⟩ := safeRuntime_block_8990_packed (by simp; omega) (by jump_dest) h8990
  have hcopy : safeRuntime_block_8990_memory (ee := I) (mem := getOwnersAllocatedMemory n)
      (x0 := UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5))
      (x1 := UInt256.lnot (UInt256.ofNat 31)) (x2 := UInt256.ofNat 128) =
        getOwnersAllocatedMemory n := by
    simp only [safeRuntime_block_8990_memory, ulit_toNat' _ hsize]
    change I.calldata.write I.calldata.size (getOwnersAllocatedMemory n) 160 _ = _
    rw [← getOwnersAllocatedMemory_size n]
    exact writePastSourceAtMemoryEnd _ _ _
  simp only [safeRuntime_block_8990_stack, hcopy] at h4076
  obtain ⟨aw', k', C', hout⟩ := safeRuntime_block_4076_packed (by omega) h4076
  simp only [safeRuntime_block_4076_stack, safeAddressMask] at hout
  have hh := twoWordHashMem_mapSlot_of_ge64 (mem := getOwnersAllocatedMemory n)
    (⟨1⟩ : UInt256) ⟨2⟩ (by rw [getOwnersAllocatedMemory_size]; decide)
  change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem ⟨1⟩ ⟨2⟩ (getOwnersAllocatedMemory n)) =
    mapSlot ⟨1⟩ ⟨2⟩ at hh
  change RD fork safeBytecode I g s0 ⟨4105⟩
    (UInt256.land solcAddrMask (solcSlotWordAt
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem ⟨1⟩ ⟨2⟩ (getOwnersAllocatedMemory n))) σ I) ::
      ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: R)
    (twoWordHashMem ⟨1⟩ ⟨2⟩ (getOwnersAllocatedMemory n)) aw' rdata σ k' C' at hout
  rw [hh, u256_land_comm solcAddrMask _] at hout
  exact ⟨_, _, _, hout⟩

theorem safeGetOwnersCountFail {I g s0 σ k C aw rdata count ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8950⟩ (count :: ret :: R) solcFreePtrMem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hn : ¬count.toNat ≤ 2 ^ 59 - 6) :
    RDrev fork safeBytecode g s0 := by
  have h8927 := safeRuntime_block_8950 (by omega) (by jump_dest) h
  simp only [safeRuntime_block_8950_stack] at h8927
  by_cases hb : count.toNat ≤ 2 ^ 64 - 1
  · obtain ⟨_, _, h8960⟩ := safeGetOwnersCountCheck h8927 (by simp; omega) hb (by jump_dest)
    obtain ⟨_, _, _, h7128⟩ := safeRuntime_block_8960_packed
      (by simp; omega) (by jump_dest) h8960
    simp only [safeRuntime_block_8960_stack] at h7128
    rw [show memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 from
      solcFreePtrMem_mload64] at h7128
    have hp : UInt256.ofNat 128 + UInt256.land
        ((UInt256.ofNat 32 + UInt256.shiftLeft count (UInt256.ofNat 5)) + UInt256.ofNat 31)
        (UInt256.lnot (UInt256.ofNat 31)) = addressArrayFreePtr count.toNat := by
      simpa only [u256_ofNat_toNat] using safeGetOwnersFinalPointer count.toNat hb
    have h7161 := safeRuntime_block_7128_taken (by simp; omega) (by
      rw [hp]
      have hv := ulit_toNat' (160 + 32 * count.toNat)
        (by change 160 + 32 * count.toNat < 2 ^ 256; omega)
      rw [ugt_one (by
        change 2 ^ 64 - 1 < (addressArrayFreePtr count.toNat).toNat
        rw [addressArrayFreePtr, hv]; omega)]
      exact u256_lor_one_left_ne_zero _) (by jump_dest) h7128
    exact safeRuntime_block_7161 (by simp [safeRuntime_block_7128_taken_stack]; omega) h7161
  · have h7161 := safeRuntime_block_8927_taken (by simp; omega)
      (by rw [ugt_one (by simpa using hb)]; decide) (by jump_dest) h8927
    exact safeRuntime_block_7161 (by simp; omega) h7161

end Benchmarks.Safe.ViaIR
