import Benchmarks.Safe.ViaIR.SetupOwnersPrefix
import Benchmarks.Safe.ViaIR.SetupOwnersStore
import Benchmarks.Safe.ViaIR.Blocks.Runtime_006

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeSetupOwnersPrepare (p : SetupOwnersInput) (evm : EVM.State)
    {I g s0 σ k C aw mem rdata ptr}
    {a b c handler len dataStart target token receiver payment : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3302⟩
      (a :: b :: c :: p.threshold :: handler :: handler :: len :: dataStart :: target :: target ::
        token :: receiver :: payment :: UInt256.ofNat ptr :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : WordArrayBuffer mem ptr p.owners)
    (hb : ptr + 32 + 32 * p.owners.length < UInt256.size) (hov : R.length + 32 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ExecFuncBody fork config p.frame evm setupOwnersFunction.body .reverted) ∨
    ∃ aw' k' C', (storedThreshold evm).toNat = 0 ∧ p.threshold.toNat ≤ p.owners.length ∧
      p.threshold.toNat ≠ 0 ∧
      RD fork safeBytecode I g s0 ⟨3333⟩
        (UInt256.ofNat ptr :: ⟨0⟩ :: ⟨1⟩ :: p.threshold :: handler :: handler :: len :: dataStart ::
          target :: target :: token :: receiver :: payment :: UInt256.ofNat p.owners.length ::
            ⟨0⟩ :: R) mem aw' rdata σ k' C' := by
  have hs : (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256)
      (fun ac ↦ ac.storage.getD (UInt256.ofNat 4) (⟨0⟩ : UInt256))) = storedThreshold evm := by
    simp only [storedThreshold, storageLoad_eq_solcSlotWord, hee, hacc]
    rfl
  by_cases hz : (storedThreshold evm).toNat = 0
  · have hzword : storedThreshold evm = ⟨0⟩ := u256_inj hz
    obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_3302_fallthrough_packed (by simp; omega)
      (by rw [hs, hzword]; rfl) h
    simp only [safeRuntime_block_3302_fallthrough_stack] at h₁
    have hlen := hm.lengthWord (by omega)
    have hn : p.owners.length < UInt256.size := by omega
    by_cases hle : p.threshold.toNat ≤ p.owners.length
    · have hgt : UInt256.gt p.threshold (memLoad (UInt256.ofNat ptr) mem) = ⟨0⟩ := by
        rw [hlen]
        exact ugt_zero (by rwa [ulit_toNat' _ hn])
      have h₂ := safeRuntime_block_3312_fallthrough (by simp; omega) hgt h₁
      by_cases hnz : p.threshold.toNat = 0
      · have hw : p.threshold = ⟨0⟩ := u256_inj hnz
        have h₃ := safeRuntime_block_3320_taken (by simp; omega)
          (by rw [hw]; decide) (by jump_dest) h₂
        have h₄ := safeRuntime_block_869 (by simp; omega) (by jump_dest) h₃
        exact .inl ⟨safeRuntime_block_9547 (by simp; omega) h₄,
          safeSetupOwnersThresholdZero p evm hz hle hnz⟩
      · have hw : p.threshold ≠ ⟨0⟩ := fun h ↦ hnz (congrArg UInt256.toNat h)
        have h₃ := safeRuntime_block_3320_fallthrough (by simp; omega)
          (isZero_eq_zero_of_ne hw) h₂
        obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeRuntime_block_3326_packed (by simp; omega) h₃
        simp only [safeRuntime_block_3326_stack, hlen] at h₄
        exact .inr ⟨_, _, _, hz, hle, hnz, h₄⟩
    · have hgt : UInt256.gt p.threshold (memLoad (UInt256.ofNat ptr) mem) = ⟨1⟩ := by
        rw [hlen]
        exact ugt_one (by rw [ulit_toNat' _ hn]; omega)
      have h₂ := safeRuntime_block_3312_taken (by simp; omega)
        (by rw [hgt]; decide) (by jump_dest) h₁
      have h₃ := safeRuntime_block_874 (by simp; omega) (by jump_dest) h₂
      exact .inl ⟨safeRuntime_block_9502 (by simp; omega) h₃,
        safeSetupOwnersThresholdTooLarge p evm hz hle⟩
  · have hw : storedThreshold evm ≠ ⟨0⟩ := fun h ↦ hz (congrArg UInt256.toNat h)
    obtain ⟨aw₁, k₁, C₁, h₁⟩ := safeRuntime_block_3302_taken_packed (by simp; omega)
      (by rw [hs]; exact hw) (by jump_dest) h
    exact .inl ⟨safeRuntime_block_3790
      (by simp [safeRuntime_block_3302_taken_stack]; omega) h₁,
      safeSetupOwnersAlreadyInitialized p evm hz⟩

end Benchmarks.Safe.ViaIR
