import Benchmarks.Safe.ViaIR.GuardReturn
import Benchmarks.Safe.ViaIR.Blocks.Runtime_008
import Benchmarks.Safe.ViaIR.Blocks.Runtime_009

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeGuardZeroTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1459⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨1484⟩ (⟨0⟩ :: ⟨0⟩ :: R) mem aw rdata σ k' C' := by
  have hr := safeRuntime_block_1459_fallthrough hov (by decide) h
  exact safeGuardSupported hr (by simp; omega)

theorem safeGuardCallSetup {I g s0 σ k C aw} {guard : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1459⟩ (guard :: R) solcFreePtrMem aw ByteArray.empty σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : guard.toNat < EVM.addressModulus)
    (hz : guard ≠ ⟨0⟩) :
    ∃ gasArg aw' k' C', RD fork safeBytecode I g s0 ⟨1637⟩
      (gasArg :: guard :: ⟨128⟩ :: ⟨36⟩ :: ⟨128⟩ :: ⟨32⟩ ::
        ⟨128⟩ :: guard :: guard :: R)
      (guardCallMemory .transaction) aw' ByteArray.empty σ k' C' := by
  have hr := safeRuntime_block_1459_taken (by omega)
    (by rw [safeAddressMask, solcAddrMask_clean hc, isZero_eq_zero_of_ne hz]; decide)
    (by jump_dest) h
  simp only [safeRuntime_block_1459_taken_stack, safeAddressMask, solcAddrMask_clean hc] at hr
  have hd := safeRuntime_block_1601 (by omega) hr
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = UInt256.ofNat 128 :=
    solcFreePtrMem_mload64
  have hm : safeRuntime_block_1601_memory (mem := solcFreePtrMem) =
      guardCallMemory .transaction := by native_decide
  rw [hm] at hd
  simp only [safeRuntime_block_1601_stack, hf] at hd
  exact ⟨_, _, _, _, hd⟩

theorem safeGuardStoreTrace {I g s0 σ k C aw mem rdata} {guard : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1484⟩ (guard :: guard :: ⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hperm : I.perm = true) :
    RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner σ guardSlot guard) ByteArray.empty := by
  have hr := safeRuntime_block_1484 (by omega) hperm h
  change RDret fork safeBytecode g s0 (sstoreAccountMap I.codeOwner σ guardSlot guard)
    (mem.readWithPadding 0 0) at hr
  simpa only [byteArray_readWithPadding_zero] using hr

theorem safeGuardStoreStatic {I g s0 σ k C aw mem rdata} {guard : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1484⟩ (guard :: R) mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hperm : I.perm = false) : RDstatic fork safeBytecode g s0 := by
  have h1 := RD.pushConst (width := 32) (op := .PUSH32) h guardSlot
    (by decide) (by native_decide) (by simp; omega)
  exact h1.sstoreStatic hperm (by native_decide) (by omega)

end Benchmarks.Safe.ViaIR
