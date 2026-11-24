import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_030
import Benchmarks.Safe.V2_0e91d99.Blocks.Runtime_036
import Benchmarks.Safe.V2_0e91d99.SetupOwnersStore
import Benchmarks.Safe.V2_0e91d99.OwnerGuardTraces

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V2_0e91d99.RuntimeBlocks

namespace Benchmarks.Safe.V2_0e91d99

set_option maxRecDepth 100000

theorem safeSetupOwnersIteration (evm : EVM.State) {p locals i current ptr}
    {I g s0 σ k C aw mem rdata} {ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8177⟩
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
      RD fork safeBytecode I g s0 ⟨8168⟩
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
  have h₁ := safeRuntime_block_8177_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h
  simp only [safeRuntime_block_8177_taken_stack] at h₁
  have hword := hm.indexWord i hi hb
  have hmask : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      current = current := by rw [safeAddressMask, solcAddrMask_clean_left hc]
  have howner : UInt256.land
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)) (UInt256.ofNat 1))
      p.owners[i] = p.owners[i] := by rw [safeAddressMask, solcAddrMask_clean_left ho]
  have hsize : 96 ≤ mem.size := by have := hm.size; omega
  by_cases he : p.owners[i] = current
  · have h₂ := safeRuntime_block_8195_fallthrough (by simp; omega)
      (by rw [hword, howner, hmask, he, u256_sub_self]; rfl) h₁
    simp only [safeRuntime_block_8195_fallthrough_stack, hword] at h₂
    have h₃ := safeRuntime_block_8231 (by simp; omega) (by jump_dest) h₂
    exact .inl ⟨safeRuntime_block_6898 (by simp; omega) h₃,
      safeSetupOwnersRepeated evm hl hi hc he⟩
  · have h₂ := safeRuntime_block_8195_taken (by simp; omega)
      (by rw [hword, howner, hmask]; exact u256_sub_ne_zero_of_ne he) (by jump_dest) h₁
    simp only [safeRuntime_block_8195_taken_stack, hword] at h₂
    have h₃ := safeRuntime_block_8247 (by simp; omega) (by jump_dest) h₂
    by_cases hv : validOwner σ I p.owners[i]
    · by_cases he0 : ownerLinkAt σ I p.owners[i] = ⟨0⟩
      · obtain ⟨mem₄, aw₄, k₄, C₄, hm₄, hr, h₄⟩ := safeCanAddOwnerCallTrace h₃
          (by simp; omega) ho (by omega) hv he0 (by jump_dest)
        obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeSetupOwnersStore evm h₄ hee hacc hc
          (by omega) hperm (by simp; omega)
        refine .inr ⟨_, aw₅, k₅, C₅,
          safeSetupOwnersStep (hperm := by simpa only [hee] using hperm) evm hl hi hc ho he (by omega) ?_ ?_, h₅, ?_, ?_⟩
        · simpa only [hee, hacc] using hv
        · simpa only [ownerLink_eq_at, hee, hacc] using he0
        · rw [twoWordHashMem_size_of_ge64 _ _ (by omega), hm₄]
        · intro off count hlo hin
          exact (twoWordHashRead _ _ _ _ _ (by omega) hlo).trans (hr off count hlo hin)
      · exact .inl ⟨safeCanAddOwnerCallTraceExisting h₃ (by simp; omega) ho (by omega) hv he0,
          safeSetupOwnersGuardRevert evm hl hi hc ho he
            (safeCanAddOwnerSourceExisting evm p.owners[i] ho
              (by simpa only [hee, hacc] using hv)
              (by simpa only [ownerLink_eq_at, hee, hacc] using he0))⟩
    · exact .inl ⟨safeCanAddOwnerCallTraceInvalid h₃ (by simp; omega) ho (by omega) hv,
        safeSetupOwnersGuardRevert evm hl hi hc ho he
          (safeCanAddOwnerSourceInvalid evm p.owners[i] ho
            (by simpa only [hee, hacc] using hv))⟩

end Benchmarks.Safe.V2_0e91d99
