import Benchmarks.Safe.Runs1e6.AddressArrayMemory
import Benchmarks.Safe.Runs1e6.ModuleStorage
import Benchmarks.Safe.Runs1e6.CheckedIncrement
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_025

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

theorem safeModulesLoopTest {I g s0 σ k C aw mem rdata index current ptr pageSize}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5870⟩
      (index :: current :: ptr :: pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hc : current.toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨5941⟩
      ((decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat)).toUInt256 ::
        index :: current :: ptr :: pageSize :: R) mem aw rdata σ k' C' := by
  have hnext : ∃ k' C', RD fork safeBytecode I g s0 ⟨5930⟩
      ((decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩)).toUInt256 ::
        index :: current :: ptr :: pageSize :: R) mem aw rdata σ k' C' := by
    by_cases hz : current = ⟨0⟩
    · have h₁ := safeRuntime_block_5870_taken (by simp; omega)
        (by rw [safeAddressMaskLiteral, solcAddrMask_clean hc, hz]; decide) (by jump_dest) h
      refine ⟨k + 10, C + 35, ?_⟩
      simpa [safeRuntime_block_5870_taken_stack, safeAddressMaskLiteral,
        solcAddrMask_clean hc, hz, UInt256.isZero] using h₁
    · have h₁ := safeRuntime_block_5870_fallthrough (by simp; omega)
        (by rw [safeAddressMaskLiteral, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
      have h₂ := safeRuntime_block_5902 (by simp; omega) h₁
      simp only [safeRuntime_block_5902_stack, safeAddressMaskLiteral, solcAddrMask_clean hc] at h₂
      by_cases hs : current = ⟨1⟩
      · refine ⟨k + 10 + 7, C + 35 + 20, ?_⟩
        simpa [hz, hs, UInt256.eq, UInt256.isZero] using h₂
      · have heq : UInt256.eq (UInt256.ofNat 1) current = ⟨0⟩ :=
          u256_eq_of_ne (Ne.symm hs)
        rw [heq] at h₂
        refine ⟨k + 10 + 7, C + 35 + 20, ?_⟩
        simpa only [heq, hz, hs, ne_eq, not_false_eq_true, and_self, decide_true]
          using h₂
  obtain ⟨k₁, C₁, h₁⟩ := hnext
  by_cases ha : current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩
  · simp only [ha.1, ha.2, ne_eq, not_false_eq_true, and_self, decide_true] at h₁
    have h₂ := safeRuntime_block_5930_fallthrough (by simp; omega) (by decide) h₁
    have h₃ := safeRuntime_block_5937 (by simp; omega) h₂
    by_cases hi : index.toNat < pageSize.toNat
    · have hlt := ult_one hi
      refine ⟨k₁ + 5 + 4, C₁ + 20 + 11, ?_⟩
      simpa only [safeRuntime_block_5937_stack, hlt, ha.1, ha.2, hi,
        ne_eq, not_false_eq_true, and_self, decide_true] using h₃
    · have hlt := ult_zero (Nat.le_of_not_lt hi)
      refine ⟨k₁ + 5 + 4, C₁ + 20 + 11, ?_⟩
      simpa only [safeRuntime_block_5937_stack, hlt, hi, and_false, decide_false]
        using h₃
  · have hf : (decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩)).toUInt256 = ⟨0⟩ := by
      simp only [ha, decide_false]; rfl
    rw [hf] at h₁
    have h₂ := safeRuntime_block_5930_taken (by simp; omega) (by decide) (by jump_dest) h₁
    have hall : ¬(current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat) :=
      fun hx ↦ ha ⟨hx.1, hx.2.1⟩
    simpa only [hall, decide_false] using ⟨_, _, h₂⟩

def modulesStepMemory (mem : ByteArray) (index : Nat) (current : UInt256) : ByteArray :=
  twoWordHashMem current ⟨1⟩ (writeWord mem (160 + 32 * index) current)

theorem safeModulesLoopStep {I g s0 σ k C aw mem rdata n words index current}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5870⟩
      (UInt256.ofNat index :: current :: ⟨128⟩ :: UInt256.ofNat n :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hn : n ≤ 2 ^ 64 - 1) (hi : index < n) (hc : current.toNat < EVM.addressModulus)
    (hz : current ≠ ⟨0⟩) (hs : current ≠ ⟨1⟩) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨5870⟩
      (UInt256.ofNat (index + 1) :: moduleLinkAt σ I current :: ⟨128⟩ :: UInt256.ofNat n :: R)
      (modulesStepMemory mem index current) aw' rdata σ k' C' := by
  have hiword := ulit_toNat' index (by change index < 2 ^ 256; omega)
  have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
  obtain ⟨k₁, C₁, h₁⟩ := safeModulesLoopTest h (by omega) hc
  simp only [hiword, hnword, hz, hs, hi, ne_eq, not_false_eq_true, and_self, decide_true] at h₁
  have h₂ := safeRuntime_block_5941_fallthrough (by simp; omega) (by decide) h₁
  have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat n :=
    mloadWordValue_of_readWithPadding (by change 128 < mem.size; have := hm.lower; omega) hm.count
  have hlt := ult_one (a := UInt256.ofNat index) (b := UInt256.ofNat n)
    (by simpa only [hiword, hnword] using hi)
  have h₃ := safeRuntime_block_5947_taken (by simp; omega)
    (by rw [hcount, hlt]; decide) (by jump_dest) h₂
  obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeRuntime_block_5965_packed
    (by simp only [safeRuntime_block_5947_taken_stack, List.length_cons]; omega)
    (by jump_dest) h₃
  simp only [safeRuntime_block_5947_taken_stack, safeRuntime_block_5965_stack,
    safeRuntime_block_5965_memory, safeAddressMaskLiteral, solcAddrMask_clean_left hc] at h₄
  have hp := safeAddressArrayIndexAddress index (by omega)
  change (UInt256.ofNat 32 + (UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat index) +
    (⟨128⟩ : UInt256))).toNat = 160 + 32 * index at hp
  rw [hp] at h₄
  rw [u256_land_comm solcAddrMask _] at h₄
  have hh := twoWordHashMem_mapSlot_of_ge64
    (mem := writeWord mem (160 + 32 * index) current) current ⟨1⟩
    (by rw [writeWord_sparse_size]; have := hm.lower; omega)
  change keccakWord ⟨0⟩ ⟨64⟩ (modulesStepMemory mem index current) = mapSlot current ⟨1⟩ at hh
  change RD fork safeBytecode I g s0 ⟨13831⟩
    (UInt256.ofNat index :: ⟨6035⟩ :: UInt256.ofNat index ::
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
  have h₆ := safeRuntime_block_6035 (by simp; omega) (by jump_dest) h₅
  refine ⟨aw₄, k₅ + 5, C₅ + 17, ?_⟩
  simpa only [safeRuntime_block_6035_stack, hinc, moduleLinkAt] using h₆

theorem safeModulesLoopExit {I g s0 σ k C aw mem rdata index current ptr pageSize}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨5870⟩
      (index :: current :: ptr :: pageSize :: R) mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hc : current.toNat < EVM.addressModulus)
    (hstop : current = ⟨0⟩ ∨ current = ⟨1⟩ ∨ pageSize.toNat ≤ index.toNat) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨6042⟩
      (index :: current :: ptr :: pageSize :: R) mem aw rdata σ k' C' := by
  obtain ⟨k₁, C₁, h₁⟩ := safeModulesLoopTest h hov hc
  have hf : ¬(current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat) := by
    rcases hstop with hz | hs | hi
    · simp [hz]
    · simp [hs]
    · omega
  simp only [hf, decide_false] at h₁
  exact ⟨_, _, safeRuntime_block_5941_taken (by simp; omega) (by decide) (by jump_dest) h₁⟩

end Benchmarks.Safe.Runs1e6
