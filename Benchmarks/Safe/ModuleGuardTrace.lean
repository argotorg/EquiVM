import Benchmarks.Safe.ModuleGuardReturn
import Benchmarks.Safe.Blocks.Runtime_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeModuleGuardZeroTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5756⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨5908⟩ (⟨0⟩ :: R) mem aw rdata σ k' C' := by
  have hr := safeRuntime_block_5756_taken hov (by native_decide) (by jump_dest) h
  exact safeModuleGuardSupported hr (by simp; omega)

theorem safeModuleGuardCallSetup {I g s0 σ k C aw} {guard : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5756⟩ (guard :: R) solcFreePtrMem aw ByteArray.empty σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : guard.toNat < EVM.addressModulus)
    (hz : guard ≠ ⟨0⟩) :
    ∃ gasArg aw' k' C', RD safeBytecode I g s0 ⟨5833⟩
      (gasArg :: guard :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨164⟩ :: ⟨33540519⟩ :: guard :: guard :: R)
      (guardCallMemory .moduleGuard) aw' ByteArray.empty σ k' C' := by
  have hr := safeRuntime_block_5756_fallthrough (by omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
  have hd := safeRuntime_block_5775 (by omega) hr
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  have hm : safeRuntime_block_5775_memory (mem := solcFreePtrMem) =
      guardCallMemory .moduleGuard := by
    native_decide
  have hf' : memLoad (UInt256.ofNat 64)
      (safeRuntime_block_5775_memory (mem := solcFreePtrMem)) = ⟨128⟩ := by
    rw [hm]
    exact guardCallMemory_mload (kind := .moduleGuard)
  dsimp only [safeRuntime_block_5775_memory] at hf'
  simp only [hf] at hf'
  rw [hm] at hd
  simp only [safeRuntime_block_5775_stack, safeAddressMask, solcAddrMask_clean hc,
    hf', hf] at hd
  exact ⟨_, _, _, _, hd⟩

theorem safeModuleGuardStoreTrace {I g s0 σ k C aw mem rdata} {guard : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5908⟩ (guard :: ⟨664⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true) :
    RDret safeBytecode g s0 (sstoreAccountMap I.codeOwner σ moduleGuardSlot guard)
      ByteArray.empty := by
  obtain ⟨_, _, hr⟩ := safeRuntime_block_5908 hov hperm (by jump_dest) h
  exact safeRuntime_block_664 (by simpa only [safeRuntime_block_5908_stack] using
    (show R.length + 0 ≤ 1024 by omega)) hr

theorem safeModuleGuardStoreStatic {I g s0 σ k C aw mem rdata} {guard : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨5908⟩ (guard :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hperm : I.perm = false) : RDstatic safeBytecode g s0 := by
  have h1 := h.jumpdest (by native_decide) (by simp; omega)
  have h2 := RD.pushConst (width := 32) (op := .PUSH32) h1 moduleGuardSlot
    (by decide) (by native_decide) (by simp; omega)
  have h3 := h2.dup2 (by native_decide) (by simp; omega)
  have h4 := h3.swap1 (by native_decide) (by simp; omega)
  exact h4.sstoreStatic hperm (by native_decide) (by simp; omega)

end Benchmarks.Safe
