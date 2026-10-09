import Benchmarks.Safe.ModuleStorage
import Benchmarks.Safe.Blocks.Runtime_017

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeModuleMembership {I g s0 σ k C aw mem rdata key ret} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2802⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', RD safeBytecode I g s0 ret
        ((addressMembership key (moduleLinkAt σ I key)).toUInt256 :: R) mem' aw' rdata σ k' C' ∧
      mem'.size = 96 ∧ mem'.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray := by
  by_cases hs : key = ⟨1⟩
  · have h₁ := safeRuntime_block_2802_taken (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc, hs]; decide) (by jump_dest) h
    have h₂ := safeRuntime_block_2853 (by omega) hret h₁
    refine ⟨mem, aw, k + 16 + 6, C + 52 + 19, ?_, hm, hread⟩
    simpa [safeRuntime_block_2853_stack, safeAddressMask, solcAddrMask_clean hc,
      addressMembership, hs, UInt256.eq] using h₂
  · have h₁ := safeRuntime_block_2802_fallthrough (by simp; omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]
          exact uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he))) h
    obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_2824_packed (by simp; omega) h₁
    have h₃ := safeRuntime_block_2853 (by omega) hret h₂
    simp only [safeRuntime_block_2853_stack, safeRuntime_block_2824_memory,
      safeAddressMask, solcAddrMask_clean_left hc] at h₃
    change RD safeBytecode I g s0 ret
      (UInt256.isZero (UInt256.isZero (UInt256.land (solcSlotWordAt
        (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key ⟨1⟩ mem)) σ I)
        solcAddrMask)) :: R) (twoWordHashMem key ⟨1⟩ mem) aw₂ rdata σ _ _ at h₃
    rw [twoWordHashMemMapSlot key ⟨1⟩ hm, normalizedNonzeroWord] at h₃
    refine ⟨_, aw₂, k₂ + 6, C₂ + 19, ?_, twoWordHashMem_size_96 key ⟨1⟩ hm,
      twoWordHashMem_read64 key ⟨1⟩ hm hread⟩
    simpa [addressMembership, moduleLinkAt, hs] using h₃

end Benchmarks.Safe
