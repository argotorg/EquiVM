import Benchmarks.Safe.PreModuleSource
import Benchmarks.Safe.Decoders
import Benchmarks.Safe.Blocks.Runtime_031
import Benchmarks.Safe.Blocks.Runtime_030

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safePreModuleUnauthorizedTrace {I g s0 σ k C aw mem rdata}
    {x : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7243⟩ (x :: R) mem aw rdata σ k C)
    (hx : x ≠ ⟨0⟩) (hov : R.length + 8 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_7243_fallthrough (by omega) (isZero_eq_zero_of_ne hx) h
  have h₂ := safeRuntime_block_7249 (by
    simp only [safeRuntime_block_7243_fallthrough_stack]; omega) (by jump_dest) h₁
  exact safeRuntime_block_6898 (by
    simp only [safeRuntime_block_7249_stack, safeRuntime_block_7243_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safePreModuleAuthorizationTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (evm : EVM.State)
    (h : RD safeBytecode I g s0 ⟨7172⟩ R mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : 64 ≤ mem.size) (hov : R.length + 10 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ¬preModuleAuthorized evm) ∨
    (preModuleAuthorized evm ∧
      ∃ aw' k' C', RD safeBytecode I g s0 ⟨7265⟩ (⟨0⟩ :: preModuleGuardWord evm :: R)
        (twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem) aw' rdata σ k' C') := by
  by_cases hs : UInt256.ofNat I.source.val = ⟨1⟩
  · obtain ⟨_, _, h₁⟩ := safeRuntime_block_7172_taken (by omega)
      (by rw [hs]; decide) (by jump_dest) h
    refine Or.inl ⟨safePreModuleUnauthorizedTrace h₁ ?_ (by
      simp only [List.length_cons]; omega), ?_⟩
    · rw [hs]; decide
    · simp [preModuleAuthorized, hee, hs]
  have hs' : UInt256.eq (UInt256.ofNat I.source.val) (UInt256.ofNat 1) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he))
  obtain ⟨_, _, h₁⟩ := safeRuntime_block_7172_fallthrough (by omega) hs' h
  obtain ⟨_, _, h₂⟩ := safeRuntime_block_7217 (by
    simp only [List.length_cons]; omega) h₁
  have hh := twoWordHashMem_mapSlot_of_ge64 (mem := mem)
    (UInt256.ofNat I.source.val) ⟨1⟩ hm
  change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem) =
    mapSlot (UInt256.ofNat I.source.val) ⟨1⟩ at hh
  have hlink : moduleLink evm (UInt256.ofNat I.source.val) =
      moduleLinkAt σ I (UInt256.ofNat I.source.val) := by
    rw [moduleLink_eq_at, hee, hacc]
  have hmem : safeRuntime_block_7217_memory (ee := I) (mem := mem) =
      twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem := rfl
  have hguard : preModuleGuardWord evm = solcSlotWordAt moduleGuardSlot σ I := by
    simp only [preModuleGuardWord, storageLoad_eq_solcSlotWord, hee, hacc]
    rfl
  simp only [safeRuntime_block_7217_stack, safeRuntime_block_7172_fallthrough_stack,
    safeAddressMask, hmem] at h₂
  change RD safeBytecode I g s0 _
    (UInt256.isZero (UInt256.land solcAddrMask
      (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩
        (twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem)) σ I)) ::
      ⟨0⟩ :: solcSlotWordAt moduleGuardSlot σ I :: R) _ _ rdata σ _ _ at h₂
  rw [hh, u256_land_comm, ← hguard] at h₂
  change RD safeBytecode I g s0 _
    (UInt256.isZero (moduleLinkAt σ I (UInt256.ofNat I.source.val)) ::
      ⟨0⟩ :: preModuleGuardWord evm :: R) _ _ rdata σ _ _ at h₂
  rw [← hlink] at h₂
  by_cases hz : moduleLink evm (UInt256.ofNat I.source.val) = ⟨0⟩
  · refine Or.inl ⟨safePreModuleUnauthorizedTrace h₂ (by rw [hz]; decide)
      (by simp; omega), ?_⟩
    simp [preModuleAuthorized, hee, hz]
  · refine Or.inr ⟨by simpa only [preModuleAuthorized, hee] using And.intro hs hz, ?_⟩
    have h₃ := safeRuntime_block_7243_taken (by simp; omega)
      (by rw [isZero_eq_zero_of_ne hz]; decide) (by jump_dest) h₂
    exact ⟨_, _, _, h₃⟩

end Benchmarks.Safe
