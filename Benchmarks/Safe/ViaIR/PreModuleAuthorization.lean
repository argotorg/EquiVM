import Benchmarks.Safe.ViaIR.PreModuleSource
import Benchmarks.Safe.ViaIR.Decoders
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044
import Benchmarks.Safe.ViaIR.Blocks.Runtime_045

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safePreModuleUnauthorizedTrace {I g s0 σ k C aw mem rdata}
    {x : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9869⟩ (x :: R) mem aw rdata σ k C)
    (hx : x ≠ ⟨0⟩) (hov : R.length + 8 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_9869_taken (by omega) hx (by jump_dest) h
  exact safeRuntime_block_10064 (by
    simp only [safeRuntime_block_9869_taken_stack]; omega) h₁

theorem safePreModuleAuthorizationTrace {I g s0 σ k C aw mem rdata}
    {target value src operation ret : UInt256} {R : List UInt256}
    (evm : EVM.State)
    (h : RD fork safeBytecode I g s0 ⟨9817⟩
      (target :: value :: src :: operation :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : 64 ≤ mem.size) (hov : R.length + 15 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬preModuleAuthorized evm) ∨
    (preModuleAuthorized evm ∧
      ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨9874⟩
        (value :: operation :: src :: ret :: ⟨0⟩ :: target :: preModuleGuardWord evm :: R)
        (twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem) aw' rdata σ k' C') := by
  by_cases hs : UInt256.ofNat I.source.val = ⟨1⟩
  · obtain ⟨_, _, h₁⟩ := safeRuntime_block_9817_fallthrough (by omega)
      (by rw [hs]; decide) h
    refine Or.inl ⟨safePreModuleUnauthorizedTrace h₁ ?_ (by
      simp only [List.length_cons]; omega), ?_⟩
    · change UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat I.source.val) ≠ ⟨0⟩
      rw [hs]; decide
    · simp [preModuleAuthorized, hee, hs]
  have hs'' : UInt256.eq (UInt256.ofNat 1) (UInt256.ofNat I.source.val) = ⟨0⟩ :=
    uInt256_eq_zero_of_ne (fun he ↦ hs (uInt256_eq_one_eq he).symm)
  obtain ⟨_, _, h₁⟩ := safeRuntime_block_9817_taken (by simp; omega)
    (by rw [hs'']; decide) (by jump_dest) h
  obtain ⟨_, _, _, h₂⟩ := safeRuntime_block_10109_packed (by
    simp only [safeRuntime_block_9817_taken_stack, List.length_cons]; omega) (by jump_dest) h₁
  have hh := twoWordHashMem_mapSlot_of_ge64 (mem := mem)
    (UInt256.ofNat I.source.val) ⟨1⟩ hm
  change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem) =
    mapSlot (UInt256.ofNat I.source.val) ⟨1⟩ at hh
  have hlink : moduleLink evm (UInt256.ofNat I.source.val) =
      moduleLinkAt σ I (UInt256.ofNat I.source.val) := by
    rw [moduleLink_eq_at, hee, hacc]
  have hmem : safeRuntime_block_10109_memory (ee := I) (mem := mem) =
      twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem := rfl
  have hguard : preModuleGuardWord evm = solcSlotWordAt moduleGuardSlot σ I := by
    simp only [preModuleGuardWord, storageLoad_eq_solcSlotWord, hee, hacc]
    rfl
  simp only [safeRuntime_block_10109_stack, safeRuntime_block_9817_taken_stack,
    safeAddressMask, hmem] at h₂
  change RD fork safeBytecode I g s0 _
    (UInt256.isZero (UInt256.land solcAddrMask
      (solcSlotWordAt (keccakWord ⟨0⟩ ⟨64⟩
        (twoWordHashMem (UInt256.ofNat I.source.val) ⟨1⟩ mem)) σ I)) ::
      value :: operation :: src :: ret :: ⟨0⟩ :: target ::
      solcSlotWordAt moduleGuardSlot σ I :: R) _ _ rdata σ _ _ at h₂
  rw [hh, u256_land_comm, ← hguard] at h₂
  change RD fork safeBytecode I g s0 _
    (UInt256.isZero (moduleLinkAt σ I (UInt256.ofNat I.source.val)) ::
      value :: operation :: src :: ret :: ⟨0⟩ :: target :: preModuleGuardWord evm :: R) _ _ rdata σ _ _ at h₂
  rw [← hlink] at h₂
  by_cases hz : moduleLink evm (UInt256.ofNat I.source.val) = ⟨0⟩
  · refine Or.inl ⟨safePreModuleUnauthorizedTrace h₂ (by rw [hz]; decide)
      (by simp; omega), ?_⟩
    simp [preModuleAuthorized, hee, hz]
  · refine Or.inr ⟨by simpa only [preModuleAuthorized, hee] using And.intro hs hz, ?_⟩
    have h₃ := safeRuntime_block_9869_fallthrough (by simp; omega) (isZero_eq_zero_of_ne hz) h₂
    exact ⟨_, _, _, h₃⟩

end Benchmarks.Safe.ViaIR
