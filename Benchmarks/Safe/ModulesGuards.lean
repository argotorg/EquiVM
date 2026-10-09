import Benchmarks.Safe.ModuleMembership
import Benchmarks.Safe.Routines
import Benchmarks.Safe.Blocks.Runtime_024
import Benchmarks.Safe.Blocks.Runtime_040

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeModulesStartCheck {I g s0 σ k C aw mem rdata start pageSize} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4815⟩ (pageSize :: start :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hc : start.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    ∃ mem' aw' k' C', RD safeBytecode I g s0 ⟨4850⟩
        ((decide (¬(start = ⟨1⟩ ∨ moduleLinkAt σ I start ≠ ⟨0⟩))).toUInt256 ::
          ⟨0⟩ :: ⟨96⟩ :: pageSize :: start :: R) mem' aw' rdata σ k' C' ∧
      mem'.size = 96 ∧ mem'.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray := by
  by_cases hs : start = ⟨1⟩
  · obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_4815_taken_packed (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc, hs]; decide) (by jump_dest) h
    refine ⟨mem, aw₁, k₁, C₁, ?_, hm, hread⟩
    simpa [safeRuntime_block_4815_taken_stack, safeAddressMask,
      solcAddrMask_clean hc, hs, UInt256.eq, UInt256.isZero] using h₁
  · have h₁ := safeRuntime_block_4815_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc]; exact u256_eq_of_ne (Ne.symm hs)) h
    have h₂ := safeRuntime_block_4839
      (by omega)
      (by jump_dest) h₁
    obtain ⟨mem', aw₃, k₃, C₃, h₃, hm', hread'⟩ := safeModuleMembership h₂
      (by simp only [safeRuntime_block_4839_stack, List.length_cons]; omega) hc hm hread
      (by jump_dest)
    have h₄ := safeRuntime_block_4848 (by simp; omega) h₃
    refine ⟨mem', aw₃, k₃ + 2, C₃ + 4, ?_, hm', hread'⟩
    by_cases hz : moduleLinkAt σ I start = ⟨0⟩ <;>
      simpa [safeRuntime_block_4848_stack, addressMembership, hs, hz, UInt256.isZero] using h₄

theorem safeModulesInvalidStart {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4850⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) :
    RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_4850_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_4856
    (by simp only [safeRuntime_block_4850_fallthrough_stack]; omega) (by jump_dest) h₁
  exact safeRuntime_block_6898 (by simp only [safeRuntime_block_4856_stack,
    safeRuntime_block_4850_fallthrough_stack, List.length_cons]; omega) h₂

theorem safeModulesZeroSize {I g s0 σ k C aw mem rdata x0 x1} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4872⟩ (x0 :: x1 :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 17 ≤ 1024) :
    RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_4872_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_4880 (by simp; omega) (by jump_dest) h₁
  exact safeRuntime_block_6898
    (by simp only [safeRuntime_block_4880_stack, List.length_cons]; omega) h₂

theorem safeModulesSizeCheck {I g s0 σ k C aw mem rdata pageSize x0 x1}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4872⟩ (x0 :: x1 :: pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hz : pageSize ≠ ⟨0⟩) :
    ∃ k' C', RD safeBytecode I g s0 ⟨4896⟩ (x0 :: x1 :: pageSize :: R)
      mem aw rdata σ k' C' := by
  exact ⟨_, _, safeRuntime_block_4872_taken (by omega) (u256_zero_sub_ne_zero hz) (by jump_dest) h⟩

theorem safeModulesLargeSize {I g s0 σ k C aw mem rdata pageSize x0 x1}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4896⟩ (x0 :: x1 :: pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hn : ¬pageSize.toNat ≤ 2 ^ 64 - 1) :
    RDrev safeBytecode g s0 := by
  have hg : UInt256.gt pageSize
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = ⟨1⟩ := ugt_one (by simpa using hn)
  have h₁ := safeRuntime_block_4896_fallthrough (by omega) (by rw [hg]; decide) h
  have h₂ := safeRuntime_block_4913
    (by simp only [safeRuntime_block_4896_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_9222
    (by simp only [safeRuntime_block_4913_stack, safeRuntime_block_4896_fallthrough_stack,
      List.length_cons]; omega) h₂

end Benchmarks.Safe
