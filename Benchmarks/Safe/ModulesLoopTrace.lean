import Benchmarks.Safe.AddressArrayMemory
import Benchmarks.Safe.ModuleStorage
import Benchmarks.Safe.CheckedIncrement
import Benchmarks.Safe.Blocks.Runtime_025

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeModulesLoopTest {I g s0 σ k C aw mem rdata index current ptr pageSize}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4995⟩
      (index :: current :: ptr :: pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hc : current.toNat < EVM.addressModulus) :
    ∃ k' C', RD safeBytecode I g s0 ⟨5040⟩
      ((decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat)).toUInt256 ::
        index :: current :: ptr :: pageSize :: R) mem aw rdata σ k' C' := by
  have hnext : ∃ k' C', RD safeBytecode I g s0 ⟨5029⟩
      ((decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩)).toUInt256 ::
        index :: current :: ptr :: pageSize :: R) mem aw rdata σ k' C' := by
    by_cases hz : current = ⟨0⟩
    · have h₁ := safeRuntime_block_4995_taken (by simp; omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
      refine ⟨k + 14, C + 47, ?_⟩
      simpa [safeRuntime_block_4995_taken_stack, safeAddressMask,
        solcAddrMask_clean hc, hz, UInt256.isZero] using h₁
    · have h₁ := safeRuntime_block_4995_fallthrough (by simp; omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
      have h₂ := safeRuntime_block_5014 (by simp; omega) h₁
      simp only [safeRuntime_block_5014_stack, safeAddressMask, solcAddrMask_clean hc] at h₂
      by_cases hs : current = ⟨1⟩
      · refine ⟨k + 14 + 11, C + 47 + 32, ?_⟩
        simpa [hz, hs, UInt256.eq, UInt256.isZero] using h₂
      · have heq : UInt256.eq (UInt256.ofNat 1) current = ⟨0⟩ :=
          u256_eq_of_ne (Ne.symm hs)
        rw [heq] at h₂
        refine ⟨k + 14 + 11, C + 47 + 32, ?_⟩
        simpa only [heq, hz, hs, ne_eq, not_false_eq_true, and_self, decide_true]
          using h₂
  obtain ⟨k₁, C₁, h₁⟩ := hnext
  by_cases ha : current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩
  · simp only [ha.1, ha.2, ne_eq, not_false_eq_true, and_self, decide_true] at h₁
    have h₂ := safeRuntime_block_5029_fallthrough (by simp; omega) (by decide) h₁
    have h₃ := safeRuntime_block_5036 (by simp; omega) h₂
    by_cases hi : index.toNat < pageSize.toNat
    · have hlt := ult_one hi
      refine ⟨k₁ + 5 + 4, C₁ + 20 + 11, ?_⟩
      simpa only [safeRuntime_block_5036_stack, hlt, ha.1, ha.2, hi,
        ne_eq, not_false_eq_true, and_self, decide_true] using h₃
    · have hlt := ult_zero (Nat.le_of_not_lt hi)
      refine ⟨k₁ + 5 + 4, C₁ + 20 + 11, ?_⟩
      simpa only [safeRuntime_block_5036_stack, hlt, hi, and_false, decide_false]
        using h₃
  · have hf : (decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩)).toUInt256 = ⟨0⟩ := by
      simp only [ha, decide_false]; rfl
    rw [hf] at h₁
    have h₂ := safeRuntime_block_5029_taken (by simp; omega) (by decide) (by jump_dest) h₁
    have hall : ¬(current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat) :=
      fun hx ↦ ha ⟨hx.1, hx.2.1⟩
    simpa only [hall, decide_false] using ⟨_, _, h₂⟩

def modulesStepMemory (mem : ByteArray) (index : Nat) (current : UInt256) : ByteArray :=
  twoWordHashMem current ⟨1⟩ (writeWord mem (160 + 32 * index) current)

theorem safeModulesLoopStep {I g s0 σ k C aw mem rdata n words index current}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4995⟩
      (UInt256.ofNat index :: current :: ⟨128⟩ :: UInt256.ofNat n :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hn : n ≤ 2 ^ 64 - 1) (hi : index < n) (hc : current.toNat < EVM.addressModulus)
    (hz : current ≠ ⟨0⟩) (hs : current ≠ ⟨1⟩) :
    ∃ aw' k' C', RD safeBytecode I g s0 ⟨4995⟩
      (UInt256.ofNat (index + 1) :: moduleLinkAt σ I current :: ⟨128⟩ :: UInt256.ofNat n :: R)
      (modulesStepMemory mem index current) aw' rdata σ k' C' := by
  have hiword := ulit_toNat' index (by change index < 2 ^ 256; omega)
  have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
  obtain ⟨k₁, C₁, h₁⟩ := safeModulesLoopTest h (by omega) hc
  simp only [hiword, hnword, hz, hs, hi, ne_eq, not_false_eq_true, and_self, decide_true] at h₁
  have h₂ := safeRuntime_block_5040_fallthrough (by simp; omega) (by decide) h₁
  have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat n :=
    mloadWordValue_of_readWithPadding (by change 128 < mem.size; have := hm.lower; omega) hm.count
  have hlt := ult_one (a := UInt256.ofNat index) (b := UInt256.ofNat n)
    (by simpa only [hiword, hnword] using hi)
  have h₃ := safeRuntime_block_5046_taken (by simp; omega)
    (by rw [hcount, hlt]; decide) (by jump_dest) h₂
  obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeRuntime_block_5064_packed
    (by simp only [safeRuntime_block_5046_taken_stack, List.length_cons]; omega)
    (by jump_dest) h₃
  simp only [safeRuntime_block_5046_taken_stack, safeRuntime_block_5064_stack,
    safeRuntime_block_5064_memory, safeAddressMask, solcAddrMask_clean_left hc] at h₄
  have hp := safeAddressArrayIndexAddress index (by omega)
  change (UInt256.ofNat 32 + (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat index) +
    (⟨128⟩ : UInt256))).toNat = 160 + 32 * index at hp
  rw [hp] at h₄
  rw [u256_land_comm solcAddrMask _] at h₄
  have hh := twoWordHashMem_mapSlot_of_ge64
    (mem := writeWord mem (160 + 32 * index) current) current ⟨1⟩
    (by rw [writeWord_sparse_size]; have := hm.lower; omega)
  change keccakWord ⟨0⟩ ⟨64⟩ (modulesStepMemory mem index current) = mapSlot current ⟨1⟩ at hh
  change RD safeBytecode I g s0 ⟨11161⟩
    (UInt256.ofNat index :: ⟨5121⟩ :: UInt256.ofNat index ::
      UInt256.land (solcSlotWordAt
        (keccakWord ⟨0⟩ ⟨64⟩ (modulesStepMemory mem index current)) σ I) solcAddrMask ::
      ⟨128⟩ :: UInt256.ofNat n :: R)
    (modulesStepMemory mem index current) aw₄ rdata σ k₄ C₄ at h₄
  rw [hh] at h₄
  obtain ⟨k₅, C₅, h₅⟩ := safeIncrementTrace h₄ (by simp; omega)
    (by rw [hiword]; change index + 1 < 2 ^ 256; omega) (by jump_dest)
  have hinc : UInt256.ofNat index + (⟨1⟩ : UInt256) = UInt256.ofNat (index + 1) := by
    apply u256_inj
    rw [uadd_toNat, hiword]
    rfl
  have h₆ := safeRuntime_block_5121 (by simp; omega) (by jump_dest) h₅
  refine ⟨aw₄, k₅ + 5, C₅ + 17, ?_⟩
  simpa only [safeRuntime_block_5121_stack, hinc, moduleLinkAt] using h₆

theorem safeModulesLoopExit {I g s0 σ k C aw mem rdata index current ptr pageSize}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨4995⟩
      (index :: current :: ptr :: pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hc : current.toNat < EVM.addressModulus)
    (hstop : current = ⟨0⟩ ∨ current = ⟨1⟩ ∨ pageSize.toNat ≤ index.toNat) :
    ∃ k' C', RD safeBytecode I g s0 ⟨5128⟩
      (index :: current :: ptr :: pageSize :: R) mem aw rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safeModulesLoopTest h hov hc
  have hf : ¬(current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat) := by
    rcases hstop with hz | hs | hi
    · simp [hz]
    · simp [hs]
    · omega
  simp only [hf, decide_false] at h₁
  exact ⟨_, _, safeRuntime_block_5040_taken (by simp; omega) (by decide) (by jump_dest) h₁⟩

end Benchmarks.Safe
