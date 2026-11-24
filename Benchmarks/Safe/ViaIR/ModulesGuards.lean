import Benchmarks.Safe.ViaIR.ModuleMembership
import Benchmarks.Safe.ViaIR.GetOwnersAllocation
import Benchmarks.Safe.ViaIR.Routines
import Benchmarks.Safe.ViaIR.Blocks.Runtime_013
import Benchmarks.Safe.ViaIR.Blocks.Runtime_014
import Benchmarks.Safe.ViaIR.Blocks.Runtime_015

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeModulesStartCheck {I g s0 σ k C aw mem rdata start} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2556⟩ (start :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : start.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    ∃ mem' aw' k' C' dummy, RD fork safeBytecode I g s0 ⟨2583⟩
        (dummy :: (decide (¬(start = ⟨1⟩ ∨ moduleLinkAt σ I start ≠ ⟨0⟩))).toUInt256 ::
          calldataWord I.calldata 36 :: start :: R) mem' aw' rdata σ k' C' ∧
      mem'.size = 96 ∧ mem'.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray := by
  by_cases hs : start = ⟨1⟩
  · have h2583 := safeRuntime_block_2556_fallthrough (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc, hs]; decide) h
    refine ⟨mem, aw, k + 20, C + 65, start, ?_, hm, hread⟩
    simpa [safeRuntime_block_2556_fallthrough_stack, safeAddressMask,
      solcAddrMask_clean hc, hs, UInt256.eq, UInt256.isZero] using h2583
  · have heq : UInt256.eq start (UInt256.ofNat 1) = ⟨0⟩ := u256_eq_of_ne hs
    have h2956 := safeRuntime_block_2556_taken (by omega)
      (by rw [safeAddressMask, solcAddrMask_clean hc, heq]; decide)
      (by jump_dest) h
    simp only [safeRuntime_block_2556_taken_stack, safeAddressMask,
      solcAddrMask_clean hc] at h2956
    have h8783 := safeRuntime_block_2956 (by simp; omega) (by jump_dest) h2956
    simp only [safeRuntime_block_2956_stack] at h8783
    obtain ⟨mem', aw', k', C', h2966, hm', hread'⟩ := safeModuleMembership h8783
      (by simp; omega) hc hm hread (by jump_dest)
    have h2583 := safeRuntime_block_2966 (by simp; omega) (by jump_dest) h2966
    refine ⟨mem', aw', k' + 5, C' + 17, ⟨0⟩, ?_, hm', hread'⟩
    by_cases hz : moduleLinkAt σ I start = ⟨0⟩ <;>
      simpa [safeRuntime_block_2966_stack, addressMembership, hs, hz, UInt256.isZero] using h2583

theorem safeModulesInvalidStart {I g s0 σ k C aw mem rdata dummy} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2583⟩ (dummy :: ⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h2911 := safeRuntime_block_2583_taken (by omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_2911
    (by simp only [safeRuntime_block_2583_taken_stack]; omega) h2911

theorem safeModulesZeroSize {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2589⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h2866 := safeRuntime_block_2589_taken (by omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_2866 (by simp; omega) h2866

theorem safeModulesSizeCheck {I g s0 σ k C aw mem rdata pageSize} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2589⟩ (pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hz : pageSize ≠ ⟨0⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨2595⟩ (pageSize :: R) mem aw rdata σ k' C' := by
  exact ⟨_, _, safeRuntime_block_2589_fallthrough hov (isZero_eq_zero_of_ne hz) h⟩

theorem safeModulesLargeSize {I g s0 σ k C aw mem rdata pageSize} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2595⟩ (pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hn : ¬pageSize.toNat ≤ 2 ^ 59 - 6)
    (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    RDrev fork safeBytecode g s0 := by
  have h8950 := safeRuntime_block_2595 (by omega) (by jump_dest) h
  simp only [safeRuntime_block_2595_stack] at h8950
  have h8927 := safeRuntime_block_8950 (by simp; omega) (by jump_dest) h8950
  simp only [safeRuntime_block_8950_stack] at h8927
  by_cases hb : pageSize.toNat ≤ 2 ^ 64 - 1
  · obtain ⟨_, _, h8960⟩ := safeGetOwnersCountCheck h8927 (by simp; omega) hb (by jump_dest)
    obtain ⟨_, _, _, h7128⟩ := safeRuntime_block_8960_packed
      (by simp; omega) (by jump_dest) h8960
    simp only [safeRuntime_block_8960_stack] at h7128
    rw [show memLoad (UInt256.ofNat 64) mem = UInt256.ofNat 128 from
      memLoad_of_wordRead _ _ _ hread] at h7128
    have hp : UInt256.ofNat 128 + UInt256.land
        ((UInt256.ofNat 32 + UInt256.shiftLeft pageSize (UInt256.ofNat 5)) + UInt256.ofNat 31)
        (UInt256.lnot (UInt256.ofNat 31)) = addressArrayFreePtr pageSize.toNat := by
      simpa only [u256_ofNat_toNat] using safeGetOwnersFinalPointer pageSize.toNat hb
    have h7161 := safeRuntime_block_7128_taken (by simp; omega) (by
      rw [hp]
      have hv := ulit_toNat' (160 + 32 * pageSize.toNat)
        (by change 160 + 32 * pageSize.toNat < 2 ^ 256; omega)
      rw [ugt_one (by
        change 2 ^ 64 - 1 < (addressArrayFreePtr pageSize.toNat).toNat
        rw [addressArrayFreePtr, hv]; omega)]
      exact u256_lor_one_left_ne_zero _) (by jump_dest) h7128
    exact safeRuntime_block_7161 (by simp [safeRuntime_block_7128_taken_stack]; omega) h7161
  · have h7161 := safeRuntime_block_8927_taken (by simp; omega)
      (by rw [ugt_one (by simpa using hb)]; decide) (by jump_dest) h8927
    exact safeRuntime_block_7161 (by simp; omega) h7161

end Benchmarks.Safe.ViaIR
