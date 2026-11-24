import Benchmarks.Safe.ViaIR.AddressArrayMemory
import Benchmarks.Safe.ViaIR.ModuleStorage
import Benchmarks.Safe.ViaIR.CheckedIncrement
import Benchmarks.Safe.ViaIR.Memory
import Benchmarks.Safe.ViaIR.Blocks.Runtime_013
import Benchmarks.Safe.ViaIR.Blocks.Runtime_014
import Benchmarks.Safe.ViaIR.Blocks.Runtime_042

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeModulesLoopTest {I g s0 σ k C aw mem rdata index current ptr pageSize}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2629⟩
      (current :: ptr :: pageSize :: index :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hc : current.toNat < EVM.addressModulus) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨2655⟩
      ((decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat)).toUInt256 ::
        current :: current :: ptr :: pageSize :: index :: R) mem aw rdata σ k' C' := by
  have hnext : ∃ k' C', RD fork safeBytecode I g s0 ⟨2649⟩
      ((decide (current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩)).toUInt256 ::
        current :: current :: ptr :: pageSize :: index :: R) mem aw rdata σ k' C' := by
    by_cases hz : current = ⟨0⟩
    · have h2649 := safeRuntime_block_2629_fallthrough (by simp; omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc, hz]; decide) h
      refine ⟨k + 15, C + 50, ?_⟩
      simpa [safeRuntime_block_2629_fallthrough_stack, safeAddressMask,
        solcAddrMask_clean hc, hz, UInt256.isZero] using h2649
    · have h2855 := safeRuntime_block_2629_taken (by simp; omega)
        (by rw [safeAddressMask, solcAddrMask_clean hc, isZero_eq_zero_of_ne hz]; decide)
        (by jump_dest) h
      simp only [safeRuntime_block_2629_taken_stack, safeAddressMask,
        solcAddrMask_clean hc] at h2855
      have h2649 := safeRuntime_block_2855 (by simp; omega) (by jump_dest) h2855
      simp only [safeRuntime_block_2855_stack] at h2649
      by_cases hs : current = ⟨1⟩
      · exact ⟨_, _, by simpa [hz, hs, UInt256.eq, UInt256.isZero] using h2649⟩
      · have heq : UInt256.eq current (UInt256.ofNat 1) = ⟨0⟩ := u256_eq_of_ne hs
        rw [heq] at h2649
        exact ⟨_, _, by simpa [hz, hs, UInt256.isZero] using h2649⟩
  obtain ⟨k₁, C₁, h2649⟩ := hnext
  by_cases ha : current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩
  · simp only [ha.1, ha.2, ne_eq, not_false_eq_true, and_self, decide_true] at h2649
    have h2846 := safeRuntime_block_2649_taken (by simp; omega) (by decide)
      (by jump_dest) h2649
    have h2655 := safeRuntime_block_2846 (by simp; omega) (by jump_dest) h2846
    simp only [safeRuntime_block_2846_stack] at h2655
    by_cases hi : index.toNat < pageSize.toNat
    · rw [ult_one hi] at h2655
      exact ⟨_, _, by simpa [ha.1, ha.2, hi] using h2655⟩
    · rw [ult_zero (Nat.le_of_not_lt hi)] at h2655
      exact ⟨_, _, by simpa [hi] using h2655⟩
  · simp only [ha, decide_false] at h2649
    have h2655 := safeRuntime_block_2649_fallthrough (by simp; omega) (by rfl) h2649
    have hall : ¬(current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat) :=
      fun hx ↦ ha ⟨hx.1, hx.2.1⟩
    exact ⟨_, _, by simpa only [hall, decide_false] using h2655⟩

def modulesStepMemory (mem : ByteArray) (index : Nat) (current : UInt256) : ByteArray :=
  twoWordHashMem current ⟨1⟩ (writeWord mem (160 + 32 * index) current)

theorem safeModulesLoopStep {I g s0 σ k C aw mem rdata n words index current}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2629⟩
      (current :: ⟨128⟩ :: UInt256.ofNat n :: UInt256.ofNat index :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hov : R.length + 13 ≤ 1024) (hm : AddressArrayMemory mem n words)
    (hn : n ≤ 2 ^ 64 - 1) (hi : index < n) (hc : current.toNat < EVM.addressModulus)
    (hz : current ≠ ⟨0⟩) (hs : current ≠ ⟨1⟩) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨2629⟩
      (moduleLinkAt σ I current :: ⟨128⟩ :: UInt256.ofNat n ::
        UInt256.ofNat (index + 1) :: ⟨0⟩ :: R)
      (modulesStepMemory mem index current) aw' rdata σ k' C' := by
  have hiword := ulit_toNat' index (by change index < 2 ^ 256; omega)
  have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
  obtain ⟨_, _, h2655⟩ := safeModulesLoopTest h (by simp; omega) hc
  simp only [hiword, hnword, hz, hs, hi, ne_eq, not_false_eq_true, and_self, decide_true]
    at h2655
  have h2661 := safeRuntime_block_2655_fallthrough (by simp; omega) (by decide) h2655
  have h9000 := safeRuntime_block_2661 (by simp; omega) (by jump_dest) h2661
  simp only [safeRuntime_block_2661_stack] at h9000
  have hcount : memLoad ⟨128⟩ mem = UInt256.ofNat n :=
    memLoad_of_wordRead _ _ _ hm.count
  have hlt := ult_one (a := UInt256.ofNat index) (b := UInt256.ofNat n)
    (by simpa only [hiword, hnword] using hi)
  have h9010 := safeRuntime_block_9000_fallthrough (by simp; omega)
    (by rw [hcount, hlt]; decide) h9000
  have h2672 := safeRuntime_block_9010 (by simp; omega) (by jump_dest) h9010
  simp only [safeRuntime_block_9010_stack] at h2672
  obtain ⟨aw', k', C', h7497⟩ := safeRuntime_block_2672_packed
    (by simp; omega) (by jump_dest) h2672
  have hp : ((UInt256.shiftLeft (UInt256.ofNat index) (UInt256.ofNat 5) +
      (⟨128⟩ : UInt256)) + UInt256.ofNat 32).toNat = 160 + 32 * index := by
    change ((UInt256.shiftLeft (UInt256.ofNat index) (UInt256.ofNat 5) + UInt256.ofNat 128) +
      UInt256.ofNat 32).toNat = _
    have hshift : UInt256.shiftLeft (UInt256.ofNat index) (UInt256.ofNat 5) =
        UInt256.ofNat (32 * index) :=
      shiftLeft5_ofNat_eq (by change 32 * index < 2 ^ 256; omega)
    rw [hshift, uadd3_ofNat_toNat (by change 32 * index < 2 ^ 256; omega) (by decide)
      (by decide) (by change 32 * index + 128 < 2 ^ 256; omega)
      (by change 32 * index + 128 + 32 < 2 ^ 256; omega)]
    omega
  simp only [safeRuntime_block_2672_stack, safeRuntime_block_2672_memory,
    safeAddressMask, hp] at h7497
  have hh := twoWordHashMem_mapSlot_of_ge64
    (mem := writeWord mem (160 + 32 * index) current) current ⟨1⟩
    (by rw [writeWord_sparse_size]; have := hm.lower; omega)
  change keccakWord ⟨0⟩ ⟨64⟩ (modulesStepMemory mem index current) = mapSlot current ⟨1⟩ at hh
  change RD fork safeBytecode I g s0 ⟨7497⟩
    (UInt256.ofNat index :: ⟨2704⟩ :: ⟨128⟩ :: UInt256.ofNat n ::
      UInt256.land solcAddrMask (solcSlotWordAt
        (keccakWord ⟨0⟩ ⟨64⟩ (modulesStepMemory mem index current)) σ I) :: ⟨0⟩ :: R)
    (modulesStepMemory mem index current) aw' rdata σ k' C' at h7497
  rw [hh, u256_land_comm solcAddrMask _] at h7497
  obtain ⟨_, _, h2704⟩ := safeIncrementTrace h7497 (by simp; omega)
    (by rw [hiword]; change index + 1 < 2 ^ 256; omega) (by jump_dest)
  have hinc : UInt256.ofNat index + (⟨1⟩ : UInt256) = UInt256.ofNat (index + 1) := by
    apply u256_inj
    rw [uadd_toNat, hiword]
    rfl
  have hout := safeRuntime_block_2704 (by simp; omega) (by jump_dest) h2704
  simp only [safeRuntime_block_2704_stack, hinc] at hout
  exact ⟨_, _, _, hout⟩

theorem safeModulesLoopExit {I g s0 σ k C aw mem rdata index current ptr pageSize}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2629⟩
      (current :: ptr :: pageSize :: index :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hc : current.toNat < EVM.addressModulus)
    (hstop : current = ⟨0⟩ ∨ current = ⟨1⟩ ∨ pageSize.toNat ≤ index.toNat) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨2710⟩
      (current :: current :: ptr :: pageSize :: index :: R) mem aw rdata σ k' C' := by
  obtain ⟨_, _, h2655⟩ := safeModulesLoopTest h hov hc
  have hf : ¬(current ≠ ⟨0⟩ ∧ current ≠ ⟨1⟩ ∧ index.toNat < pageSize.toNat) := by
    rcases hstop with hz | hs | hi
    · simp [hz]
    · simp [hs]
    · omega
  simp only [hf, decide_false] at h2655
  exact ⟨_, _, safeRuntime_block_2655_taken (by simp; omega) (by decide) (by jump_dest) h2655⟩

end Benchmarks.Safe.ViaIR
