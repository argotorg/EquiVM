import Benchmarks.Safe.SetupOwnersPrefix
import Benchmarks.Safe.SetupOwnersStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSetupOwnersPrepare (p : SetupOwnersInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7975⟩
      (p.threshold :: UInt256.ofNat ptr :: ret :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : WordArrayBuffer mem ptr p.owners)
    (hb : ptr + 32 + 32 * p.owners.length < UInt256.size) (hov : R.length + 20 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧ ExecFuncBody config p.frame evm setupOwnersFunction.body .reverted) ∨
    ∃ aw' k' C', (storedThreshold evm).toNat = 0 ∧ p.threshold.toNat ≤ p.owners.length ∧
      p.threshold.toNat ≠ 0 ∧
      RD safeBytecode I g s0 ⟨8057⟩
        (⟨0⟩ :: UInt256.ofNat p.owners.length :: ⟨1⟩ :: p.threshold ::
          UInt256.ofNat ptr :: ret :: R) mem aw' rdata σ k' C' := by
  have hs : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) = storedThreshold evm := by
    simp only [storedThreshold, storageLoad_eq_solcSlotWord, hee, hacc]
    rfl
  by_cases hz : (storedThreshold evm).toNat = 0
  · have hzword : storedThreshold evm = ⟨0⟩ := u256_inj hz
    obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_7975_taken_packed (by simp; omega)
      (by rw [hs, hzword]; decide) (by jump_dest) h
    have hlen := hm.lengthWord (by omega)
    have hn : p.owners.length < UInt256.size := by omega
    by_cases hle : p.threshold.toNat ≤ p.owners.length
    · have hgt : UInt256.gt p.threshold (memLoad (UInt256.ofNat ptr) mem) = ⟨0⟩ := by
        rw [hlen]
        exact ugt_zero (by rwa [ulit_toNat' _ hn])
      have h₂ := safeRuntime_block_8000_taken (by simp; omega)
        (by rw [hgt]; decide) (by jump_dest) h₁
      by_cases hnz : p.threshold.toNat = 0
      · have hw : p.threshold = ⟨0⟩ := u256_inj hnz
        have h₃ := safeRuntime_block_8026_fallthrough (by simp; omega)
          (by rw [hw]; rfl) h₂
        have h₄ := safeRuntime_block_8034 (by simp; omega) (by jump_dest) h₃
        exact .inl ⟨safeRuntime_block_6898 (by simp; omega) h₄,
          safeSetupOwnersThresholdZero p evm hz hle hnz⟩
      · have hw : p.threshold ≠ ⟨0⟩ := fun h ↦ hnz (congrArg UInt256.toNat h)
        have h₃ := safeRuntime_block_8026_taken (by simp; omega)
          (u256_zero_sub_ne_zero hw) (by jump_dest) h₂
        have h₄ := safeRuntime_block_8050 (by simp; omega) h₃
        simp only [safeRuntime_block_8050_stack, hlen] at h₄
        exact .inr ⟨_, _, _, hz, hle, hnz, h₄⟩
    · have hgt : UInt256.gt p.threshold (memLoad (UInt256.ofNat ptr) mem) = ⟨1⟩ := by
        rw [hlen]
        exact ugt_one (by rw [ulit_toNat' _ hn]; omega)
      have h₂ := safeRuntime_block_8000_fallthrough (by simp; omega) (by rw [hgt]; rfl) h₁
      have h₃ := safeRuntime_block_8010 (by simp; omega) (by jump_dest) h₂
      exact .inl ⟨safeRuntime_block_6898 (by simp; omega) h₃,
        safeSetupOwnersThresholdTooLarge p evm hz hle⟩
  · have hw : storedThreshold evm ≠ ⟨0⟩ := fun h ↦ hz (congrArg UInt256.toNat h)
    obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_7975_fallthrough_packed (by simp; omega)
      (by rw [hs]; exact isZero_eq_zero_of_ne hw) h
    have h₂ := safeRuntime_block_7984 (by simp; omega) (by jump_dest) h₁
    exact .inl ⟨safeRuntime_block_6898 (by simp; omega) h₂,
      safeSetupOwnersAlreadyInitialized p evm hz⟩

end Benchmarks.Safe
