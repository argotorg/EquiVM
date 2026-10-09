import Benchmarks.Safe.GuardReturn
import Benchmarks.Safe.Blocks.Runtime_006

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeGuardZeroTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6006⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 4 ≤ 1024) :
    ∃ k' C', RD safeBytecode I g s0 ⟨6158⟩ (⟨0⟩ :: R) mem aw rdata σ k' C' := by
  have hr := safeRuntime_block_6006_taken hov (by native_decide) (by jump_dest) h
  exact safeGuardSupported hr (by simp; omega)

theorem safeGuardCallSetup {I g s0 σ k C aw} {guard : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6006⟩ (guard :: R) solcFreePtrMem aw ByteArray.empty σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : guard.toNat < EVM.addressModulus)
    (hz : guard ≠ ⟨0⟩) :
    ∃ gasArg aw' k' C', RD safeBytecode I g s0 ⟨6083⟩
      (gasArg :: guard :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨164⟩ :: ⟨33540519⟩ :: guard :: guard :: R)
      (guardCallMemory .transaction) aw' ByteArray.empty σ k' C' := by
  have hr := safeRuntime_block_6006_fallthrough (by omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc]; exact isZero_eq_zero_of_ne hz) h
  have hd := safeRuntime_block_6025 (by omega) hr
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  have hm : safeRuntime_block_6025_memory (mem := solcFreePtrMem) =
      guardCallMemory .transaction := by
    native_decide
  have hf' : memLoad (UInt256.ofNat 64)
      (safeRuntime_block_6025_memory (mem := solcFreePtrMem)) = ⟨128⟩ := by
    rw [hm]
    exact guardCallMemory_mload (kind := .transaction)
  dsimp only [safeRuntime_block_6025_memory] at hf'
  simp only [hf] at hf'
  rw [hm] at hd
  simp only [safeRuntime_block_6025_stack, safeAddressMask, solcAddrMask_clean hc,
    hf', hf] at hd
  exact ⟨_, _, _, _, hd⟩

theorem safeGuardStoreTrace {I g s0 σ k C aw mem rdata} {guard : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6158⟩ (guard :: ⟨664⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true) :
    RDret safeBytecode g s0 (sstoreAccountMap I.codeOwner σ guardSlot guard) ByteArray.empty := by
  obtain ⟨_, _, hr⟩ := safeRuntime_block_6158 hov hperm (by jump_dest) h
  exact safeRuntime_block_664 (by simpa only [safeRuntime_block_6158_stack] using
    (show R.length + 0 ≤ 1024 by omega)) hr

theorem safeGuardStoreStatic {I g s0 σ k C aw mem rdata} {guard : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6158⟩ (guard :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hperm : I.perm = false) : RDstatic safeBytecode g s0 := by
  have h1 := h.jumpdest (by native_decide) (by simp; omega)
  have h2 := RD.pushConst (width := 32) (op := .PUSH32) h1 guardSlot
    (by decide) (by native_decide) (by simp; omega)
  have h3 := h2.dup2 (by native_decide) (by simp; omega)
  have h4 := h3.swap1 (by native_decide) (by simp; omega)
  exact h4.sstoreStatic hperm (by native_decide) (by simp; omega)

end Benchmarks.Safe
