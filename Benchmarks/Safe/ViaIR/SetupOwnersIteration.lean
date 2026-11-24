import Benchmarks.Safe.ViaIR.SetupOwnersStore
import Benchmarks.Safe.ViaIR.OwnerGuardTraces
import Benchmarks.Safe.ViaIR.Blocks.Runtime_017
import Benchmarks.Safe.ViaIR.Blocks.Runtime_042

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000
set_option maxHeartbeats 800000

theorem safeSetupOwnersIteration (evm : EVM.State) {p locals i current ptr}
    {I g s0 σ k C aw mem rdata}
    {handler len dataStart target token receiver payment : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨3686⟩
      (UInt256.ofNat ptr :: UInt256.ofNat i :: current :: p.threshold :: handler :: handler ::
        len :: dataStart :: target :: target :: token :: receiver :: payment ::
          UInt256.ofNat p.owners.length :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hl : SetupOwnersLocals p locals i current) (hi : i < p.owners.length)
    (hee : evm.executionEnv = I) (hacc : evm.accountMap = σ)
    (hm : WordArrayBuffer mem ptr p.owners) (hp : 96 ≤ ptr)
    (hb : ptr + 32 + 32 * p.owners.length < UInt256.size)
    (hc : current.toNat < EVM.addressModulus) (ho : p.owners[i].toNat < EVM.addressModulus)
    (hperm : I.perm = true) (hov : R.length + 32 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ExecBlock fork config { contract := contract, locals := locals } evm setupOwnersLoopBody
        .reverted) ∨
    ∃ mem' aw' k' C',
      ExecBlock fork config { contract := contract, locals := locals } evm setupOwnersLoopBody
        (.ok { contract := contract, locals := setupOwnersNextLocals locals p.owners[i] i }
          (writeOwnerLink evm current p.owners[i])) ∧
      RD fork safeBytecode I g s0 ⟨3333⟩
        (UInt256.ofNat ptr :: UInt256.ofNat (i + 1) :: p.owners[i] :: p.threshold :: handler ::
          handler :: len :: dataStart :: target :: target :: token :: receiver :: payment ::
            UInt256.ofNat p.owners.length :: ⟨0⟩ :: R) mem' aw' rdata
        (writeOwnerLink evm current p.owners[i]).accountMap k' C' ∧
      mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) := by
  have hn : p.owners.length < UInt256.size := by omega
  have hlt : UInt256.lt (UInt256.ofNat i) (memLoad (UInt256.ofNat ptr) mem) = ⟨1⟩ := by
    rw [hm.lengthWord (by omega)]
    exact ult_one (by rw [ulit_toNat' i (by omega), ulit_toNat' _ hn]; exact hi)
  have h₀ := safeRuntime_block_3686 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_3686_stack, safeAddressMask] at h₀
  have ha := safeRuntime_block_9000_fallthrough (by simp; omega)
    (by rw [hlt]; decide) h₀
  have h₁ := safeRuntime_block_9010 (by simp; omega) (by jump_dest) ha
  simp only [safeRuntime_block_9010_stack] at h₁
  have hidx : ((UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
      UInt256.ofNat ptr) + UInt256.ofNat 32).toNat = ptr + 32 + 32 * i := by
    have hshift : UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) =
        UInt256.ofNat (32 * i) := shiftLeft5_ofNat_eq (by omega)
    rw [hshift, uadd3_ofNat_toNat (by omega) (by omega) (by decide) (by omega) (by omega)]
    omega
  have hword : memLoad ((UInt256.shiftLeft (UInt256.ofNat i) (UInt256.ofNat 5) +
      UInt256.ofNat ptr) + UInt256.ofNat 32) mem = p.owners[i] := by
    rw [memLoadReadWord, hidx, hm.words i hi, uInt256OfByteArray_toByteArray]
  by_cases he : p.owners[i] = current
  · have h₂ := safeRuntime_block_3704_taken (by simp; omega)
      (by rw [hword, safeAddressMask, solcAddrMask_clean_left hc, solcAddrMask_clean ho, he]
          simp [UInt256.eq]; decide) (by jump_dest) h₁
    simp only [safeRuntime_block_3704_taken_stack] at h₂
    have h₃ := safeRuntime_block_3785 (by simp; omega) (by jump_dest) h₂
    exact .inl ⟨safeRuntime_block_9637 (by simp; omega) h₃,
      safeSetupOwnersRepeated evm hl hi hc he⟩
  have h₂ := safeRuntime_block_3704_fallthrough (by simp; omega)
    (by rw [hword, safeAddressMask, solcAddrMask_clean_left hc, solcAddrMask_clean ho]
        exact u256_eq_of_ne he) h₁
  simp only [safeRuntime_block_3704_fallthrough_stack, hword, safeAddressMask,
    solcAddrMask_clean_left hc, solcAddrMask_clean ho] at h₂
  have h₃ := safeRuntime_block_3724 (by simp; omega) (by jump_dest) h₂
  simp only [safeRuntime_block_3724_stack] at h₃
  have hsize : 96 ≤ mem.size := by have := hm.size; omega
  by_cases hv : validOwner σ I p.owners[i]
  · by_cases he0 : ownerLinkAt σ I p.owners[i] = ⟨0⟩
    · obtain ⟨mem₄, aw₄, k₄, C₄, hm₄, hr₄, h₄⟩ := safeCanAddOwnerHeapTrace h₃
        (by simp; omega) ho hsize hv he0 (by jump_dest)
      obtain ⟨aw₅, k₅, C₅, h₅⟩ := safeSetupOwnersStore evm h₄ hee hacc
        (by omega) hperm (by simp; omega)
      refine .inr ⟨twoWordHashMem current ⟨2⟩ mem₄, aw₅, k₅, C₅,
        safeSetupOwnersStep (hperm := by simpa only [hee] using hperm) evm hl hi hc ho he (by omega) ?_ ?_, h₅, ?_, ?_⟩
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

end Benchmarks.Safe.ViaIR
