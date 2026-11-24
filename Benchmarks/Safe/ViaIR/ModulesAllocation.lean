import Benchmarks.Safe.ViaIR.ModulesGuards
import Benchmarks.Safe.ViaIR.AddressArrayMemory
import Benchmarks.Safe.ViaIR.Memory

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

def modulesAllocatedMemory (mem : ByteArray) (n : Nat) : ByteArray :=
  writeWord (writeWord mem 64 (addressArrayFreePtr n)) 128 (UInt256.ofNat n)

theorem modulesAllocatedMemory_size (mem : ByteArray) (n : Nat) (hm : mem.size = 96) :
    (modulesAllocatedMemory mem n).size = 160 := by
  simp only [modulesAllocatedMemory, writeWord_sparse_size, hm]
  decide +kernel

theorem safeModulesAllocated (mem : ByteArray) (n : Nat) (hm : mem.size = 96) :
    AddressArrayMemory (modulesAllocatedMemory mem n) n (List.replicate n ⟨0⟩) := by
  have hs := modulesAllocatedMemory_size mem n hm
  have hinner : (writeWord mem 64 (addressArrayFreePtr n)).size = 96 := by
    simp only [writeWord_sparse_size, hm]
    decide
  refine ⟨List.length_replicate, by rw [hs], by omega, by omega, ?_, ?_, ?_⟩
  · rw [modulesAllocatedMemory,
      writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by decide, by rw [hinner]⟩)]
    exact writeWord_sparse_read_back _ _ _
  · exact writeWord_sparse_read_back _ _ _
  · exact WordArrayMemory.zeroes _ _ _ (by omega)

theorem safeModulesAllocationMemory (mem : ByteArray) (n : Nat) :
    safeRuntime_block_8973_memory
      (mem := safeRuntime_block_7157_memory (mem := mem)
        (x0 := addressArrayFreePtr n)) (x0 := UInt256.ofNat 128) (x2 := UInt256.ofNat n) =
      modulesAllocatedMemory mem n := by rfl

set_option maxHeartbeats 800000 in
theorem safeModulesAllocate {I g s0 σ k C aw mem rdata n start} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2595⟩
      (UInt256.ofNat n :: start :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) (hn : n ≤ 2 ^ 59 - 6)
    (hsize : I.calldata.size < UInt256.size)
    (hm : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨2629⟩
      (moduleLinkAt σ I start :: ⟨128⟩ :: UInt256.ofNat n :: ⟨0⟩ :: ⟨0⟩ :: R)
      (twoWordHashMem start ⟨1⟩ (modulesAllocatedMemory mem n)) aw' rdata σ k' C' := by
  have hb : n ≤ 2 ^ 64 - 1 := by omega
  have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
  have hp := safeGetOwnersFinalPointer n hb
  have h8950 := safeRuntime_block_2595 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_2595_stack] at h8950
  have h8927 := safeRuntime_block_8950 (by simp; omega) (by jump_dest) h8950
  simp only [safeRuntime_block_8950_stack] at h8927
  obtain ⟨_, _, h8960⟩ := safeGetOwnersCountCheck h8927 (by simp; omega)
    (by rwa [hnword]) (by jump_dest)
  obtain ⟨_, _, _, h7128⟩ := safeRuntime_block_8960_packed (by simp; omega) (by jump_dest) h8960
  simp only [safeRuntime_block_8960_stack] at h7128
  rw [show memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 128 from
    memLoad_of_wordRead _ _ _ hread] at h7128
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
  simp only [safeRuntime_block_8973_stack, safeModulesAllocationMemory] at hcount
  obtain ⟨_, _, h8990⟩ := safeGetOwnersCountCheck hcount (by simp; omega)
    (by rwa [hnword]) (by jump_dest)
  obtain ⟨_, _, _, h2603⟩ := safeRuntime_block_8990_packed (by simp; omega) (by jump_dest) h8990
  have hcopy : safeRuntime_block_8990_memory (ee := I) (mem := modulesAllocatedMemory mem n)
      (x0 := UInt256.ofNat 32 + UInt256.shiftLeft (UInt256.ofNat n) (UInt256.ofNat 5))
      (x1 := UInt256.lnot (UInt256.ofNat 31)) (x2 := UInt256.ofNat 128) =
        modulesAllocatedMemory mem n := by
    simp only [safeRuntime_block_8990_memory, ulit_toNat' _ hsize]
    change I.calldata.write I.calldata.size (modulesAllocatedMemory mem n) 160 _ = _
    rw [← modulesAllocatedMemory_size mem n hm]
    exact writePastSourceAtMemoryEnd _ _ _
  simp only [safeRuntime_block_8990_stack, hcopy] at h2603
  obtain ⟨aw', k', C', hout⟩ := safeRuntime_block_2603_packed (by omega) h2603
  simp only [safeRuntime_block_2603_stack, safeAddressMask] at hout
  have hh := twoWordHashMem_mapSlot_of_ge64 (mem := modulesAllocatedMemory mem n)
    start ⟨1⟩ (by rw [modulesAllocatedMemory_size mem n hm]; decide)
  change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem start ⟨1⟩ (modulesAllocatedMemory mem n)) =
    mapSlot start ⟨1⟩ at hh
  change RD fork safeBytecode I g s0 ⟨2629⟩
    (UInt256.land solcAddrMask (solcSlotWordAt
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem start ⟨1⟩ (modulesAllocatedMemory mem n))) σ I) ::
      ⟨128⟩ :: UInt256.ofNat n :: ⟨0⟩ :: ⟨0⟩ :: R)
    (twoWordHashMem start ⟨1⟩ (modulesAllocatedMemory mem n)) aw' rdata σ k' C' at hout
  rw [hh, u256_land_comm solcAddrMask _] at hout
  exact ⟨_, _, _, hout⟩

end Benchmarks.Safe.ViaIR
