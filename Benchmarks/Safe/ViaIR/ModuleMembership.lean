import Benchmarks.Safe.ViaIR.ModuleStorage
import Benchmarks.Safe.ViaIR.Blocks.Runtime_040
import Benchmarks.Safe.ViaIR.Blocks.Runtime_041

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

theorem safeModuleMembership {I g s0 σ k C aw mem rdata key ret} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8783⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', RD fork safeBytecode I g s0 ret
        ((addressMembership key (moduleLinkAt σ I key)).toUInt256 :: R) mem' aw' rdata σ k' C' ∧
      mem'.size = 96 ∧ mem'.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray := by
  by_cases hs : key = ⟨1⟩
  · have h8804 := safeRuntime_block_8783_fallthrough (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean_left hc, hs]; decide) h
    have hdone := safeRuntime_block_8804 (by omega) hret h8804
    refine ⟨mem, aw, k + 15 + 3, C + 50 + 13, ?_, hm, hread⟩
    simpa [safeRuntime_block_8804_stack, safeRuntime_block_8783_fallthrough_stack,
      safeAddressMask, solcAddrMask_clean_left hc, addressMembership, hs, UInt256.eq] using hdone
  · have heq : UInt256.eq key (UInt256.ofNat 1) = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he))
    have h8807 := safeRuntime_block_8783_taken (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean_left hc, heq]; decide) (by jump_dest) h
    simp only [safeRuntime_block_8783_taken_stack, safeAddressMask,
      solcAddrMask_clean_left hc] at h8807
    obtain ⟨aw', k', C', hdone⟩ := safeRuntime_block_8807_packed (by omega) hret h8807
    simp only [safeRuntime_block_8807_stack, safeRuntime_block_8807_memory,
      safeAddressMask] at hdone
    change RD fork safeBytecode I g s0 ret
      (UInt256.isZero (UInt256.isZero (UInt256.land solcAddrMask (solcSlotWordAt
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key ⟨1⟩ mem)) σ I))) :: R)
      (twoWordHashMem key ⟨1⟩ mem) aw' rdata σ k' C' at hdone
    rw [twoWordHashMemMapSlot key ⟨1⟩ hm, u256_land_comm solcAddrMask _,
      normalizedNonzeroWord] at hdone
    refine ⟨_, aw', k', C', ?_, twoWordHashMem_size_96 key ⟨1⟩ hm,
      twoWordHashMem_read64 key ⟨1⟩ hm hread⟩
    simpa [addressMembership, moduleLinkAt, hs] using hdone

end Benchmarks.Safe.ViaIR
