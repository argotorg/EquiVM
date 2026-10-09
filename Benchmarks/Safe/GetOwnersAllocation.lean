import Benchmarks.Safe.GetOwnersLoopTrace
import Benchmarks.Safe.Memory
import Benchmarks.Safe.Blocks.Runtime_022
import Benchmarks.Safe.Blocks.Runtime_040

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 2000

theorem safeGetOwnersAllocationMemory (n : Nat) (hn : n ≤ 2 ^ 64 - 1) :
    safeRuntime_block_4318_taken_memory (mem := solcFreePtrMem) (x0 := UInt256.ofNat n) =
      addressArrayAllocatedMemory solcFreePtrMem n := by
  simp only [safeRuntime_block_4318_taken_memory,
    show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64,
      addressArrayFreePtr_eq n hn]
  rfl

set_option maxHeartbeats 800000 in
theorem safeGetOwnersAllocate {I g s0 σ k C aw rdata n} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4318⟩
      (UInt256.ofNat n :: ⟨0⟩ :: R) solcFreePtrMem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hn : n ≤ 2 ^ 64 - 1)
    (hsize : I.calldata.size < UInt256.size) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨4419⟩
      (ownerLinkAt σ I ⟨1⟩ :: ⟨0⟩ :: ⟨128⟩ :: R)
      (twoWordHashMem ⟨1⟩ ⟨2⟩ (addressArrayAllocatedMemory solcFreePtrMem n)) aw' rdata σ k' C' :=
        by
  have hmem := safeGetOwnersAllocationMemory n hn
  have hstart : ∃ aw' k' C' x, RD safeBytecode I g s0 ⟨4359⟩
      (x :: ⟨128⟩ :: ⟨0⟩ :: R) (addressArrayAllocatedMemory solcFreePtrMem n) aw' rdata σ k' C' :=
        by
    by_cases hz : n = 0
    · obtain ⟨aw', k', C', h'⟩ := safeRuntime_block_4318_taken_packed (by simp; omega)
        (by rw [hz]; decide) (by jump_dest) h
      simp only [safeRuntime_block_4318_taken_stack,
        show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64,
        hmem] at h'
      exact ⟨_, _, _, _, h'⟩
    · have hnz : UInt256.ofNat n ≠ ⟨0⟩ := by
        intro he
        have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
        have := congrArg UInt256.toNat he
        change (UInt256.ofNat n).toNat = 0 at this
        exact hz (hnword.symm.trans this)
      obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_4318_fallthrough_packed
        (by simp; omega) (isZero_eq_zero_of_ne hnz) h
      change safeRuntime_block_4318_fallthrough_memory (mem := solcFreePtrMem)
        (x0 := UInt256.ofNat n) = addressArrayAllocatedMemory solcFreePtrMem n at hmem
      simp only [safeRuntime_block_4318_fallthrough_stack,
        show memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ from solcFreePtrMem_mload64,
        hmem] at h₁
      obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_4344_packed (by simp; omega) h₁
      have hcopy : safeRuntime_block_4344_memory (ee := I)
          (mem := addressArrayAllocatedMemory solcFreePtrMem n) (x0 := UInt256.ofNat n) (x1 :=
            ⟨128⟩) =
          addressArrayAllocatedMemory solcFreePtrMem n := by
        simp only [safeRuntime_block_4344_memory, ulit_toNat' _ hsize]
        change I.calldata.write I.calldata.size (addressArrayAllocatedMemory solcFreePtrMem n) 160
          _ = _
        rw [← safeAddressArrayAllocatedSize solcFreePtrMem n solcFreePtrMem_size]
        exact writePastSourceAtMemoryEnd _ _ _
      rw [hcopy] at h₂
      exact ⟨_, _, _, _, h₂⟩
  obtain ⟨aw₁, k₁, C₁, x, h₁⟩ := hstart
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_4359_packed (by omega) h₁
  simp only [safeRuntime_block_4359_stack, safeAddressMask, ← safeOwnerSentinelSlot] at h₂
  change RD safeBytecode I g s0 ⟨4419⟩
    (UInt256.land solcAddrMask (solcSlotWordAt (mapSlot ⟨1⟩ ⟨2⟩) σ I) ::
      ⟨0⟩ :: ⟨128⟩ :: R) (twoWordHashMem ⟨1⟩ ⟨2⟩ (addressArrayAllocatedMemory solcFreePtrMem n))
    aw₂ rdata σ k₂ C₂ at h₂
  rw [u256_land_comm solcAddrMask _] at h₂
  exact ⟨_, _, _, h₂⟩

theorem safeGetOwnersCountCheck {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4289⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hn : (solcSlotWordAt ⟨3⟩ σ I).toNat ≤ 2 ^ 64 - 1) :
    ∃ k' C', RD safeBytecode I g s0 ⟨4318⟩
      (solcSlotWordAt ⟨3⟩ σ I :: ⟨0⟩ :: ⟨96⟩ :: R) mem aw rdata σ k' C' := by
  have hg : UInt256.gt (solcSlotWordAt ⟨3⟩ σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = ⟨0⟩ := ugt_zero hn
  exact safeRuntime_block_4289_taken hov (by
    change UInt256.isZero (UInt256.gt (solcSlotWordAt ⟨3⟩ σ I) _) ≠ _
    rw [hg]; decide)
    (by jump_dest) h

theorem safeGetOwnersCountFail {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4289⟩ R mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hn : ¬(solcSlotWordAt ⟨3⟩ σ I).toNat ≤ 2 ^ 64 - 1) :
    RDrev safeBytecode g s0 := by
  have hg : UInt256.gt (solcSlotWordAt ⟨3⟩ σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = ⟨1⟩ := ugt_one (by simpa using hn)
  obtain ⟨k₁, C₁, h₁⟩ := safeRuntime_block_4289_fallthrough hov
    (by change UInt256.isZero (UInt256.gt (solcSlotWordAt ⟨3⟩ σ I) _) = _
        rw [hg]; decide) h
  have h₂ := safeRuntime_block_4311
    (by simp only [safeRuntime_block_4289_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_9222
    (by simp only [safeRuntime_block_4289_fallthrough_stack,
      safeRuntime_block_4311_stack, List.length_cons]; omega) h₂

end Benchmarks.Safe
