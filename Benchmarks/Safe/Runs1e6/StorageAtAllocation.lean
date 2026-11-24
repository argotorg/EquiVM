import Benchmarks.Safe.Runs1e6.StorageAtGas
import Benchmarks.Safe.Runs1e6.AddressArrayMemory
import Benchmarks.Safe.Runs1e6.Memory
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_018
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_040

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 2000

def storageAtAllocatedMemory (bytes : UInt256) : ByteArray :=
  writeWord (writeWord solcFreePtrMem 128 bytes) 64
    (UInt256.ofNat 128 + (UInt256.ofNat 32 +
      UInt256.land (UInt256.lnot (UInt256.ofNat 31)) (UInt256.ofNat 31 + bytes)))

theorem storageAtAllocatedMemory_size (bytes : UInt256) :
    (storageAtAllocatedMemory bytes).size = 160 := by
  simp only [storageAtAllocatedMemory, writeWord_sparse_size, solcFreePtrMem_size]
  decide +kernel

theorem safeStorageAtAllocationMemory (bytes : UInt256) :
    safeRuntime_block_3545_taken_memory (mem := solcFreePtrMem) (x0 := bytes) =
      storageAtAllocatedMemory bytes := by
  simp only [safeRuntime_block_3545_taken_memory,
    show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64]
  rfl

theorem safeStorageAtAllocate {I g s0 σ k C aw rdata bytes len offset}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3545⟩
      (bytes :: ⟨0⟩ :: ⟨96⟩ :: len :: offset :: R) solcFreePtrMem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hsize : I.calldata.size < UInt256.size) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨3592⟩
      (⟨0⟩ :: ⟨128⟩ :: ⟨96⟩ :: len :: offset :: R)
      (storageAtAllocatedMemory bytes) aw' rdata σ k' C' := by
  have hmem := safeStorageAtAllocationMemory bytes
  have hstart : ∃ aw' k' C' x, RD fork safeBytecode I g s0 ⟨3587⟩
      (x :: ⟨128⟩ :: ⟨0⟩ :: ⟨96⟩ :: len :: offset :: R)
      (storageAtAllocatedMemory bytes) aw' rdata σ k' C' := by
    by_cases hz : bytes = ⟨0⟩
    · obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_3545_taken_packed (by simp; omega)
        (by rw [hz]; decide) (by jump_dest) h
      simp only [safeRuntime_block_3545_taken_stack,
        show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64,
        hmem] at h'
      exact ⟨_, _, _, _, h'⟩
    · obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_3545_fallthrough_packed
        (by simp; omega) (isZero_eq_zero_of_ne hz) h
      change safeRuntime_block_3545_fallthrough_memory (mem := solcFreePtrMem)
        (x0 := bytes) = storageAtAllocatedMemory bytes at hmem
      simp only [safeRuntime_block_3545_fallthrough_stack,
        show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64,
        hmem] at h₁
      obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_3575_packed (by simp; omega) h₁
      have hcopy : safeRuntime_block_3575_memory (ee := I)
          (mem := storageAtAllocatedMemory bytes) (x0 := bytes) (x1 := ⟨128⟩) =
          storageAtAllocatedMemory bytes := by
        simp only [safeRuntime_block_3575_memory, ulit_toNat' _ hsize]
        change I.calldata.write I.calldata.size (storageAtAllocatedMemory bytes) 160 _ = _
        rw [← storageAtAllocatedMemory_size bytes]
        exact writePastSourceAtMemoryEnd _ _ _
      rw [hcopy] at h₂
      exact ⟨_, _, _, _, h₂⟩
  obtain ⟨aw₁, k₁, C₁, x, h₁⟩ := hstart
  have h₂ := safeRuntime_block_3587 (by simp; omega) h₁
  exact ⟨_, _, _, h₂⟩

theorem safeStorageAtLengthCheck {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3513⟩ (len :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hn : (UInt256.shiftLeft len (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 1) :
    RD fork safeBytecode I g s0 ⟨3545⟩
      (UInt256.shiftLeft len (UInt256.ofNat 5) :: ⟨0⟩ :: ⟨96⟩ :: len :: R)
      mem aw rdata σ (k + 13) (C + 43) := by
  have hg : UInt256.gt (UInt256.shiftLeft len (UInt256.ofNat 5))
      (UInt256.ofNat 18446744073709551615) = ⟨0⟩ := ugt_zero hn
  exact safeRuntime_block_3513_taken (by omega) (by rw [hg]; decide) (by jump_dest) h

theorem safeStorageAtLengthFail {I g s0 σ k C aw mem rdata len} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3513⟩ (len :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024)
    (hn : ¬(UInt256.shiftLeft len (UInt256.ofNat 5)).toNat ≤ 2 ^ 64 - 1) :
    RDrev fork safeBytecode g s0 := by
  have hg : UInt256.gt (UInt256.shiftLeft len (UInt256.ofNat 5))
      (UInt256.ofNat 18446744073709551615) = ⟨1⟩ := ugt_one (by simpa using hn)
  have h₁ := safeRuntime_block_3513_fallthrough (by omega) (by rw [hg]; decide) h
  have h₂ := safeRuntime_block_3538
    (by simp only [safeRuntime_block_3513_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11708
    (by simp only [safeRuntime_block_3513_fallthrough_stack,
      safeRuntime_block_3538_stack, List.length_cons]; omega) h₂

theorem storageAtAllocatedMemory_wordBuffer (n : Nat) (hn : n ≤ 2 ^ 64 - 1) :
    storageAtAllocatedMemory (UInt256.ofNat (32 * n)) =
      wordBufferAllocatedMemory solcFreePtrMem n (UInt256.ofNat (32 * n)) := by
  rw [storageAtAllocatedMemory, wordAlignedRoundUp (32 * n)
    (by change 32 * n + 31 < 2 ^ 256; omega) (by omega)]
  have hp : UInt256.ofNat 128 + (UInt256.ofNat 32 + UInt256.ofNat (32 * n)) =
      addressArrayFreePtr n := by
    apply u256_inj
    rw [uadd_toNat, uadd_toNat, ulit_toNat' (32 * n)
      (by change 32 * n < 2 ^ 256; omega)]
    change (128 + (32 + 32 * n) % UInt256.size) % UInt256.size = _
    rw [Nat.mod_eq_of_lt (show 32 + 32 * n < UInt256.size by
      change 32 + 32 * n < 2 ^ 256; omega),
      Nat.mod_eq_of_lt (show 128 + (32 + 32 * n) < UInt256.size by
        change 128 + (32 + 32 * n) < 2 ^ 256; omega)]
    simpa only [addressArrayFreePtr, ← Nat.add_assoc] using
      (ulit_toNat' (160 + 32 * n) (by change 160 + 32 * n < 2 ^ 256; omega)).symm
  rw [hp]
  rfl

end Benchmarks.Safe.Runs1e6
