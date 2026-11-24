import Benchmarks.Safe.Runs1e6.ModuleMembership
import Benchmarks.Safe.Runs1e6.Routines
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_024
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_030
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_040

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

theorem safeModulesStartCheck {I g s0 σ k C aw mem rdata start pageSize} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5615⟩ (pageSize :: start :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hc : start.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    ∃ mem' aw' k' C', RD fork safeBytecode I g s0 ⟨5663⟩
        ((decide (¬(start = ⟨1⟩ ∨ moduleLinkAt σ I start ≠ ⟨0⟩))).toUInt256 ::
          ⟨0⟩ :: ⟨96⟩ :: pageSize :: start :: R) mem' aw' rdata σ k' C' ∧
      mem'.size = 96 ∧ mem'.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray := by
  by_cases hs : start = ⟨1⟩
  · obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_5615_taken_packed (by omega)
      (by rw [safeAddressMaskLiteral, solcAddrMask_clean hc, hs]; decide) (by jump_dest) h
    refine ⟨mem, aw₁, k₁, C₁, ?_, hm, hread⟩
    simpa [safeRuntime_block_5615_taken_stack, safeAddressMaskLiteral,
      solcAddrMask_clean hc, hs, UInt256.eq, UInt256.isZero] using h₁
  · have h₁ := safeRuntime_block_5615_fallthrough (by omega)
      (by rw [safeAddressMaskLiteral, solcAddrMask_clean hc]; exact u256_eq_of_ne (Ne.symm hs)) h
    have h₂ := safeRuntime_block_5652
      (by omega)
      (by jump_dest) h₁
    obtain ⟨mem', aw₃, k₃, C₃, h₃, hm', hread'⟩ := safeModuleMembership h₂
      (by simp only [safeRuntime_block_5652_stack, List.length_cons]; omega) hc hm hread
      (by jump_dest)
    have h₄ := safeRuntime_block_5661 (by simp; omega) h₃
    refine ⟨mem', aw₃, k₃ + 2, C₃ + 4, ?_, hm', hread'⟩
    by_cases hz : moduleLinkAt σ I start = ⟨0⟩ <;>
      simpa [safeRuntime_block_5661_stack, addressMembership, hs, hz, UInt256.isZero] using h₄

theorem safeModulesInvalidStart {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5663⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_5663_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_5669
    (by simp only [safeRuntime_block_5663_fallthrough_stack]; omega) (by jump_dest) h₁
  exact safeRuntime_block_8421 (by simp only [safeRuntime_block_5669_stack,
    safeRuntime_block_5663_fallthrough_stack, List.length_cons]; omega) h₂

theorem safeModulesZeroSize {I g s0 σ k C aw mem rdata x0 x1} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5709⟩ (x0 :: x1 :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 17 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_5709_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_5717 (by simp; omega) (by jump_dest) h₁
  exact safeRuntime_block_8421
    (by simp only [safeRuntime_block_5717_stack, List.length_cons]; omega) h₂

theorem safeModulesSizeCheck {I g s0 σ k C aw mem rdata pageSize x0 x1}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5709⟩ (x0 :: x1 :: pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hz : pageSize ≠ ⟨0⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨5757⟩ (x0 :: x1 :: pageSize :: R)
      mem aw rdata σ k' C' := by
  exact ⟨_, _, safeRuntime_block_5709_taken (by omega) (u256_zero_sub_ne_zero hz) (by jump_dest) h⟩

theorem safeModulesLargeSize {I g s0 σ k C aw mem rdata pageSize x0 x1}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5757⟩ (x0 :: x1 :: pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 8 ≤ 1024) (hn : ¬pageSize.toNat ≤ 2 ^ 64 - 1) :
    RDrev fork safeBytecode g s0 := by
  have hg : UInt256.gt pageSize
      (UInt256.ofNat 18446744073709551615) = ⟨1⟩ := ugt_one (by simpa using hn)
  have h₁ := safeRuntime_block_5757_fallthrough (by omega) (by rw [hg]; decide) h
  have h₂ := safeRuntime_block_5775
    (by simp only [safeRuntime_block_5757_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11708
    (by simp only [safeRuntime_block_5775_stack, safeRuntime_block_5757_fallthrough_stack,
      List.length_cons]; omega) h₂

end Benchmarks.Safe.Runs1e6
