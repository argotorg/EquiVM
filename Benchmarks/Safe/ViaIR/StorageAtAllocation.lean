import Benchmarks.Safe.ViaIR.StorageAtGas
import Benchmarks.Safe.ViaIR.AddressArrayMemory
import Benchmarks.Safe.ViaIR.Memory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_034

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

def storageAtAllocatedMemory (bytes : UInt256) : ByteArray :=
  writeWord (writeWord solcFreePtrMem 64 (UInt256.ofNat (160 + bytes.toNat))) 128 bytes

theorem storageAtAllocatedMemory_size (bytes : UInt256) :
    (storageAtAllocatedMemory bytes).size = 160 := by
  simp only [storageAtAllocatedMemory, writeWord_sparse_size, solcFreePtrMem_size]
  decide +kernel

theorem safeStorageAtRoundedWord (bytes : UInt256) (hn : bytes.toNat ≤ 2 ^ 64 - 1)
    (ha : bytes.toNat % 32 = 0) :
    UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (UInt256.ofNat 31 + bytes) = bytes := by
  simpa only [u256_ofNat_toNat] using
    wordAlignedRoundUp bytes.toNat (by change bytes.toNat + 31 < 2 ^ 256; omega) ha

theorem safeStorageAtShiftAligned (len : UInt256) :
    (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat % 32 = 0 := by
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ (UInt256.ofNat 5).val ≥ 256)]
  change ((len.toNat <<< 5) % UInt256.size) % 32 = 0
  rw [Nat.shiftLeft_eq, Nat.mod_mod_of_dvd _ (by decide : 32 ∣ UInt256.size)]
  simp

theorem safeStorageAtFinalPointer (bytes : UInt256) (hn : bytes.toNat ≤ 2 ^ 64 - 1)
    (ha : bytes.toNat % 32 = 0) :
    UInt256.ofNat 128 + UInt256.land
      ((UInt256.ofNat 32 + bytes) + UInt256.ofNat 31) (UInt256.lnot (UInt256.ofNat 31)) =
        UInt256.ofNat (160 + bytes.toNat) := by
  have halloc : UInt256.ofNat 32 + bytes = UInt256.ofNat (bytes.toNat + 32) := by
    simpa only [u256_ofNat_toNat] using u256_32_add_ofNat bytes.toNat
  rw [halloc, u256_land_comm, u256_add_comm (UInt256.ofNat (bytes.toNat + 32)),
    wordAlignedRoundUp (bytes.toNat + 32)
      (by change bytes.toNat + 32 + 31 < 2 ^ 256; omega) (by omega)]
  apply u256_inj
  change (UInt256.add (UInt256.ofNat 128) (UInt256.ofNat (bytes.toNat + 32))).toNat = _
  rw [uadd_ofNat_toNat (by decide) (by change bytes.toNat + 32 < 2 ^ 256; omega)
    (by change 128 + (bytes.toNat + 32) < 2 ^ 256; omega),
    ulit_toNat' _ (by change 160 + bytes.toNat < 2 ^ 256; omega)]
  omega

theorem safeStorageAtAllocationMemory (bytes : UInt256) :
    safeRuntime_block_6141_memory
      (mem := safeRuntime_block_7157_memory (mem := solcFreePtrMem)
        (x0 := UInt256.ofNat (160 + bytes.toNat))) (x0 := bytes) (x3 := ⟨128⟩) =
      storageAtAllocatedMemory bytes := by rfl

theorem safeStorageAtLengthCheck {I g s0 σ k C aw mem rdata bytes ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7181⟩ (bytes :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hn : bytes.toNat ≤ 2 ^ 64 - 1)
    (ha : bytes.toNat % 32 = 0) (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret ((UInt256.ofNat 32 + bytes) :: R)
      mem aw rdata σ k' C' := by
  have h7196 := safeRuntime_block_7181_fallthrough (by simp; omega) (ugt_zero hn) h
  have hout := safeRuntime_block_7196 (by omega) hret h7196
  simp only [safeRuntime_block_7196_stack, safeStorageAtRoundedWord bytes hn ha] at hout
  exact ⟨_, _, hout⟩

theorem safeStorageAtAllocate {I g s0 σ k C aw rdata bytes len offset} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6127⟩
      ((UInt256.ofNat 32 + bytes) :: offset :: len :: bytes :: R)
      solcFreePtrMem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hsize : I.calldata.size < UInt256.size)
    (hn : bytes.toNat ≤ 2 ^ 64 - 161) (ha : bytes.toNat % 32 = 0) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨6165⟩ (⟨0⟩ :: offset :: len :: ⟨128⟩ :: R)
      (storageAtAllocatedMemory bytes) aw' rdata σ k' C' := by
  have hb : bytes.toNat ≤ 2 ^ 64 - 1 := by omega
  have hp := safeStorageAtFinalPointer bytes hb ha
  obtain ⟨_, _, _, h7128⟩ := safeRuntime_block_6127_packed (by omega) (by jump_dest) h
  simp only [safeRuntime_block_6127_stack] at h7128
  rw [show memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 from
    solcFreePtrMem_mload64] at h7128
  have h7157 := safeRuntime_block_7128_fallthrough (by simp; omega) (by
    rw [hp]
    have hv : (UInt256.ofNat (160 + bytes.toNat)).toNat = 160 + bytes.toNat :=
      ulit_toNat' _ (by change 160 + bytes.toNat < 2 ^ 256; omega)
    rw [ugt_zero (by rw [hv]; change 160 + bytes.toNat ≤ 2 ^ 64 - 1; omega),
      ult_zero (by rw [hv]; change 128 ≤ 160 + bytes.toNat; omega), u256_lor_zero]
    rfl) h7128
  simp only [safeRuntime_block_7128_fallthrough_stack, hp] at h7157
  obtain ⟨_, _, _, h6141⟩ := safeRuntime_block_7157_packed (by simp; omega) (by jump_dest) h7157
  simp only [safeRuntime_block_7157_stack] at h6141
  obtain ⟨_, _, _, h7181⟩ := safeRuntime_block_6141_packed (by simp; omega) (by jump_dest) h6141
  simp only [safeRuntime_block_6141_stack] at h7181
  change RD fork _ _ _ _ _ _ (storageAtAllocatedMemory bytes) _ _ _ _ _ at h7181
  obtain ⟨_, _, h6156⟩ := safeStorageAtLengthCheck h7181 (by simp; omega) hb ha (by jump_dest)
  obtain ⟨_, _, _, h6165⟩ := safeRuntime_block_6156_packed (by omega) h6156
  have hcopy : safeRuntime_block_6156_memory (ee := I)
      (mem := storageAtAllocatedMemory bytes) (x0 := UInt256.ofNat 32 + bytes)
      (x1 := UInt256.lnot (UInt256.ofNat 31)) (x4 := UInt256.ofNat 128) =
        storageAtAllocatedMemory bytes := by
    simp only [safeRuntime_block_6156_memory, ulit_toNat' _ hsize]
    change I.calldata.write I.calldata.size (storageAtAllocatedMemory bytes) 160 _ = _
    rw [← storageAtAllocatedMemory_size bytes]
    exact writePastSourceAtMemoryEnd _ _ _
  simp only [safeRuntime_block_6156_stack] at h6165
  rw [hcopy] at h6165
  exact ⟨_, _, _, h6165⟩

theorem safeStorageAtLengthFail {I g s0 σ k C aw rdata bytes len offset} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7181⟩
      (bytes :: ⟨6127⟩ :: offset :: len :: bytes :: R) solcFreePtrMem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (ha : bytes.toNat % 32 = 0)
    (hn : ¬bytes.toNat ≤ 2 ^ 64 - 161) : RDrev fork safeBytecode g s0 := by
  by_cases hb : bytes.toNat ≤ 2 ^ 64 - 1
  · obtain ⟨_, _, h6127⟩ := safeStorageAtLengthCheck h (by simp; omega) hb ha (by jump_dest)
    obtain ⟨_, _, _, h7128⟩ := safeRuntime_block_6127_packed (by omega) (by jump_dest) h6127
    simp only [safeRuntime_block_6127_stack] at h7128
    rw [show memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 from
      solcFreePtrMem_mload64] at h7128
    have h7161 := safeRuntime_block_7128_taken (by simp; omega) (by
      rw [safeStorageAtFinalPointer bytes hb ha]
      have hv := ulit_toNat' (160 + bytes.toNat)
        (by change 160 + bytes.toNat < 2 ^ 256; omega)
      rw [ugt_one (by rw [hv]; change 2 ^ 64 - 1 < 160 + bytes.toNat; omega)]
      exact u256_lor_one_left_ne_zero _) (by jump_dest) h7128
    exact safeRuntime_block_7161
      (by simp [safeRuntime_block_7128_taken_stack]; omega) h7161
  · have h7161 := safeRuntime_block_7181_taken (by simp; omega)
      (by rw [ugt_one (by simpa using hb)]; decide) (by jump_dest) h
    exact safeRuntime_block_7161 (by simp; omega) h7161

theorem storageAtAllocatedMemory_wordBuffer (n : Nat) (hn : n ≤ 2 ^ 64 - 1) :
    AddressArrayMemory (storageAtAllocatedMemory (UInt256.ofNat (32 * n))) n
      (List.replicate n ⟨0⟩) (UInt256.ofNat (32 * n)) := by
  have hs := storageAtAllocatedMemory_size (UInt256.ofNat (32 * n))
  have hm : (writeWord solcFreePtrMem 64 (addressArrayFreePtr n)).size = 96 := by
    simp only [writeWord_sparse_size, solcFreePtrMem_size]
    decide
  have hmem : storageAtAllocatedMemory (UInt256.ofNat (32 * n)) =
      writeWord (writeWord solcFreePtrMem 64 (addressArrayFreePtr n)) 128
        (UInt256.ofNat (32 * n)) := by
    rw [storageAtAllocatedMemory, ulit_toNat' _ (by change 32 * n < 2 ^ 256; omega)]
    rfl
  refine ⟨List.length_replicate, by rw [hs], by omega, by omega, ?_, ?_, ?_⟩
  · rw [hmem, writeWord_sparse_read_preserved _ _ _ _ (.inl ⟨by decide, by rw [hm]⟩)]
    exact writeWord_sparse_read_back _ _ _
  · rw [hmem]
    exact writeWord_sparse_read_back _ _ _
  · exact WordArrayMemory.zeroes _ _ _ (by omega)

end Benchmarks.Safe.ViaIR
