import Benchmarks.Safe.SetupOwnersStore
import Benchmarks.Safe.OwnerGuardTraces

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSetupOwnersIteration (evm : EVM.State) {p locals i current ptr}
    {I g s0 σ k C aw mem rdata} {ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8066⟩
      (UInt256.ofNat i :: UInt256.ofNat p.owners.length :: current :: p.threshold ::
        UInt256.ofNat ptr :: ret :: R) mem aw rdata σ k C)
    (hl : SetupOwnersLocals p locals i current) (hi : i < p.owners.length)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : WordArrayBuffer mem ptr p.owners) (hp : 96 ≤ ptr)
    (hb : ptr + 32 + 32 * p.owners.length < UInt256.size)
    (hc : current.toNat < EVM.addressModulus) (ho : p.owners[i].toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 20 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ExecBlock config { contract := contract, locals := locals } evm setupOwnersLoopBody
        .reverted) ∨
    ∃ mem' aw' k' C',
      ExecBlock config { contract := contract, locals := locals } evm setupOwnersLoopBody
        (.ok { contract := contract, locals := setupOwnersNextLocals locals p.owners[i] i }
          (writeOwnerLink evm current p.owners[i])) ∧
      RD safeBytecode I g s0 ⟨8057⟩
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
  have h₁ := safeRuntime_block_8066_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h
  simp only [safeRuntime_block_8066_taken_stack] at h₁
  have hword := hm.indexWord i hi hb
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      current = current := by rw [safeAddressMask, solcAddrMask_clean_left hc]
  have howner : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      p.owners[i] = p.owners[i] := by rw [safeAddressMask, solcAddrMask_clean_left ho]
  by_cases he : p.owners[i] = current
  · have h₂ := safeRuntime_block_8084_fallthrough (by simp; omega)
      (by rw [hword, hmask, howner, he, u256_sub_self]; rfl) h₁
    simp only [safeRuntime_block_8084_fallthrough_stack, hword] at h₂
    have h₃ := safeRuntime_block_8120 (by simp; omega) (by jump_dest) h₂
    exact .inl ⟨safeRuntime_block_6898 (by simp; omega) h₃,
      safeSetupOwnersRepeated evm hl hi hc he⟩
  have h₂ := safeRuntime_block_8084_taken (by simp; omega)
    (by rw [hword, hmask, howner]; exact u256_sub_ne_zero_of_ne he) (by jump_dest) h₁
  simp only [safeRuntime_block_8084_taken_stack, hword] at h₂
  have h₃ := safeRuntime_block_8136 (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_8136_stack] at h₃
  have hsize : 96 ≤ mem.size := by have := hm.size; omega
  by_cases hv : validOwner σ I p.owners[i]
  · by_cases he0 : ownerLinkAt σ I p.owners[i] = ⟨0⟩
    · obtain ⟨mem₄, aw₄, k₄, C₄, hm₄, hr₄, h₄⟩ := safeCanAddOwnerHeapTrace h₃
        (by simp; omega) ho hsize hv he0 (by jump_dest)
      obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeSetupOwnersStore evm h₄ hee hacc hc
        (by omega) hperm (by omega)
      refine .inr ⟨twoWordHashMem current ⟨2⟩ mem₄, aw₅, k₅, C₅,
        safeSetupOwnersStep evm hl hi hc ho he (by omega) ?_ ?_, h₅, ?_, ?_⟩
      · simpa only [hee, hacc] using hv
      · simpa only [ownerLink_eq_at, hee, hacc] using he0
      · rw [twoWordHashMem_size_of_ge64 _ _ (by omega), hm₄]
      · intro off count hlo hin
        rw [twoWordHashRead _ _ _ _ _ (by omega) hlo, hr₄ off count hlo hin]
    · exact .inl ⟨safeCanAddOwnerHeapTraceExisting h₃ (by simp; omega) ho hsize hv he0,
        safeSetupOwnersGuardRevert evm hl hi hc ho he
          (safeCanAddOwnerSourceExisting evm p.owners[i] ho
            (by simpa only [hee, hacc] using hv)
            (by simpa only [ownerLink_eq_at, hee, hacc] using he0))⟩
  · exact .inl ⟨safeCanAddOwnerTraceInvalid h₃ (by simp; omega) ho (by omega) hv,
      safeSetupOwnersGuardRevert evm hl hi hc ho he
        (safeCanAddOwnerSourceInvalid evm p.owners[i] ho (by simpa only [hee, hacc] using hv))⟩

end Benchmarks.Safe
