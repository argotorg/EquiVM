import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_014
import Benchmarks.Safe.V0_cdb2eb5.SetupOwnersStore
import Benchmarks.Safe.V0_cdb2eb5.OwnerGuardTraces
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_030
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_036
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_037

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem safeSetupOwnersIteration (evm : EVM.State) {p locals i current ptr}
    {I g s0 σ k C aw mem rdata} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8234⟩
      (UInt256.ofNat i :: UInt256.ofNat p.owners.length :: current :: p.threshold ::
        UInt256.ofNat ptr :: ret :: R) mem aw rdata σ k C)
    (hl : SetupOwnersLocals p locals i current) (hi : i < p.owners.length)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : WordArrayBuffer mem ptr p.owners) (hp : 96 ≤ ptr)
    (hb : ptr + 32 + 32 * p.owners.length < UInt256.size)
    (hc : current.toNat < EVM.addressModulus) (ho : p.owners[i].toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 20 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecBlock fork config { contract := contract, locals := locals } evm setupOwnersLoopBody
        .reverted) ∨
    ∃ mem' aw' k' C',
      ExecBlock fork config { contract := contract, locals := locals } evm setupOwnersLoopBody
        (.ok { contract := contract, locals := setupOwnersNextLocals locals p.owners[i] i }
          (writeOwnerLink evm current p.owners[i])) ∧
      RD fork safeBytecode I g s0 ⟨8225⟩
        (UInt256.ofNat (i + 1) :: UInt256.ofNat p.owners.length :: p.owners[i] :: p.threshold ::
          UInt256.ofNat ptr :: ret :: R) mem' aw' rdata
        (writeOwnerLink evm current p.owners[i]).accountMap k' C' ∧
      mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) := by
  have hn : p.owners.length < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (memLoad (UInt256.ofNat ptr) mem) = ⟨1⟩ := by
    rw [hm.lengthWord (by omega)]
    exact ult_one (by rw [ulit_toNat' i (by omega), ulit_toNat' _ hn]; exact hi)
  have h₁ := safeRuntime_block_8234_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h
  simp only [safeRuntime_block_8234_taken_stack] at h₁
  have hword := hm.indexWord i hi hb
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      current = current := by rw [safeAddressMask, solcAddrMask_clean_left hc]
  have howner : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      p.owners[i] = p.owners[i] := by rw [safeAddressMask, solcAddrMask_clean_left ho]
  have hzero : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      (⟨0⟩ : UInt256) = ⟨0⟩ := by native_decide
  have hsize : 96 ≤ mem.size := by have := hm.size; omega
  by_cases hv : validOwner σ I p.owners[i]
  · have hz : UInt256.eq p.owners[i] ⟨0⟩ = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun he ↦ hv.1 (uInt256_eq_one_eq he))
    have hs : UInt256.eq (UInt256.ofNat 1) p.owners[i] = ⟨0⟩ :=
      uInt256_eq_zero_of_ne (fun he ↦ hv.2 (uInt256_eq_one_eq he).symm)
    have h₂ := safeRuntime_block_8252_fallthrough (by simp; omega)
      (by rw [hword, howner, hzero]; exact hz) h₁
    have h₃ := safeRuntime_block_8289 (by simp [safeRuntime_block_8252_fallthrough_stack]; omega) h₂
    simp only [safeRuntime_block_8289_stack, safeRuntime_block_8252_fallthrough_stack,
      hword, safeAddressMask, solcAddrMask_clean ho, hs] at h₃
    have h₄ := safeRuntime_block_8303_taken (by simp; omega) (by decide) (by jump_dest) h₃
    simp only [safeRuntime_block_8303_taken_stack] at h₄
    by_cases he : p.owners[i] = current
    · have h₅ := safeRuntime_block_8325_taken (by simp; omega)
        (by rw [howner, hmask, he, uInt256_eq_self]; decide) (by jump_dest) h₄
      simp only [safeRuntime_block_8325_taken_stack, howner, hmask, he, uInt256_eq_self] at h₅
      have h₆ := safeRuntime_block_8381_fallthrough (by simp; omega) (by decide) h₅
      have h₇ := safeRuntime_block_8387
        (by simp [safeRuntime_block_8381_fallthrough_stack]; omega) (by jump_dest) h₆
      exact .inl ⟨safeRuntime_block_6990
        (by simp [safeRuntime_block_8381_fallthrough_stack]; omega) h₇,
        safeSetupOwnersRepeated evm hl hi hc he⟩
    · have h₅ := safeRuntime_block_8325_fallthrough (by simp; omega)
        (by
          rw [howner, hmask]
          exact uInt256_eq_zero_of_ne (fun hh ↦ he (uInt256_eq_one_eq hh))) h₄
      obtain ⟨aw₆, k₆, C₆, h₆⟩ := safeRuntime_block_8352_packed
        (by simp [safeRuntime_block_8325_fallthrough_stack]; omega) h₅
      have hcheck := safeCanAddOwnerHeapCheckWord σ I p.owners[i] mem ho
      simp only [safeRuntime_block_1797_taken_memory, solcSlotWordAt] at hcheck
      simp only [safeRuntime_block_8352_stack, safeRuntime_block_8352_memory,
        safeRuntime_block_8325_fallthrough_stack] at h₆
      rw [hcheck] at h₆
      simp only [howner] at h₆
      change RD fork safeBytecode I g s0 ⟨8381⟩ _ (twoWordHashMem p.owners[i] ⟨2⟩ mem)
        aw₆ rdata σ k₆ C₆ at h₆
      by_cases he0 : ownerLinkAt σ I p.owners[i] = ⟨0⟩
      · have h₇ := safeRuntime_block_8381_taken (by simp; omega)
          (by rw [he0]; decide) (by jump_dest) h₆
        simp only [safeRuntime_block_8381_taken_stack] at h₇
        obtain ⟨aw₈, k₈, C₈, h₈⟩ := safeSetupOwnersStore evm h₇ hee hacc hc
          (by omega) hperm (by simp; omega)
        have hm₆ : (twoWordHashMem p.owners[i] ⟨2⟩ mem).size = mem.size :=
          twoWordHashMem_size_of_ge64 _ _ (by omega)
        refine .inr ⟨_, aw₈, k₈, C₈,
          safeSetupOwnersStep (hperm := by simpa only [hee] using hperm) evm hl hi hc ho he (by omega) ?_ ?_, h₈, ?_, ?_⟩
        · simpa only [hee, hacc] using hv
        · simpa only [ownerLink_eq_at, hee, hacc] using he0
        · rw [twoWordHashMem_size_of_ge64 _ _ (by omega), hm₆]
        · intro off count hlo hin
          rw [twoWordHashRead _ _ _ _ _ (by omega) hlo,
            twoWordHashRead _ _ _ _ _ hin hlo]
      · have h₇ := safeRuntime_block_8381_fallthrough (by simp; omega)
          (by rw [isZero_eq_zero_of_ne he0]; rfl) h₆
        have h₈ := safeRuntime_block_8387
          (by simp [safeRuntime_block_8381_fallthrough_stack]; omega) (by jump_dest) h₇
        exact .inl ⟨safeRuntime_block_6990
          (by simp [safeRuntime_block_8381_fallthrough_stack]; omega) h₈,
          safeSetupOwnersGuardRevert evm hl hi hc ho he
            (safeCanAddOwnerSourceExisting evm p.owners[i] ho
              (by simpa only [hee, hacc] using hv)
              (by simpa only [ownerLink_eq_at, hee, hacc] using he0))⟩
  · have hbad : ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨8303⟩
        (⟨1⟩ :: p.owners[i] :: UInt256.ofNat i :: UInt256.ofNat p.owners.length :: current ::
          p.threshold :: UInt256.ofNat ptr :: ret :: R) mem aw' rdata σ k' C' := by
      by_cases hz : p.owners[i] = ⟨0⟩
      · have h₂ := safeRuntime_block_8252_taken (by simp; omega)
          (by rw [hword, howner, hz]; native_decide) (by jump_dest) h₁
        simp only [safeRuntime_block_8252_taken_stack, hword, howner, hz,
          hzero, uInt256_eq_self] at h₂
        exact ⟨_, _, _, by simpa only [hz] using h₂⟩
      · have hs : p.owners[i] = ⟨1⟩ := by
          by_contra hs
          exact hv ⟨hz, hs⟩
        have h₂ := safeRuntime_block_8252_fallthrough (by simp; omega)
          (by rw [hword, howner, hs]; native_decide) h₁
        have h₃ := safeRuntime_block_8289
          (by simp [safeRuntime_block_8252_fallthrough_stack]; omega) h₂
        simp only [safeRuntime_block_8289_stack, safeRuntime_block_8252_fallthrough_stack,
          hword, safeAddressMask, solcAddrMask_clean ho] at h₃
        have heq : UInt256.eq (UInt256.ofNat 1) p.owners[i] = ⟨1⟩ := by rw [hs]; rfl
        rw [heq] at h₃
        exact ⟨_, _, _, h₃⟩
    obtain ⟨_, _, _, h₂⟩ := hbad
    have h₃ := safeRuntime_block_8303_fallthrough (by simp; omega) (by decide) h₂
    have h₄ := safeRuntime_block_8309
      (by simp [safeRuntime_block_8303_fallthrough_stack]; omega) (by jump_dest) h₃
    have hrev := safeRuntime_block_6990
      (by simp [safeRuntime_block_8303_fallthrough_stack]; omega) h₄
    refine .inl ⟨hrev, ?_⟩
    by_cases he : p.owners[i] = current
    · exact safeSetupOwnersRepeated evm hl hi hc he
    · exact safeSetupOwnersGuardRevert evm hl hi hc ho he
        (safeCanAddOwnerSourceInvalid evm p.owners[i] ho (by simpa only [hee, hacc] using hv))

end Benchmarks.Safe.V0_cdb2eb5
