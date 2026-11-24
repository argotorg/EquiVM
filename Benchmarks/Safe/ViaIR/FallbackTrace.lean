import Benchmarks.Safe.ViaIR.FallbackMemory
import Benchmarks.Safe.ViaIR.ByteCopy

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

theorem safeFallbackPrepare {I g s0 σ k C rdata}
    {handler : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨66⟩ (handler :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ aw gasArg k' C', RD fork safeBytecode I g s0 ⟨92⟩
      (gasArg :: handler :: ⟨0⟩ :: ⟨128⟩ ::
        (UInt256.ofNat I.calldata.size + UInt256.ofNat 20) :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨128⟩ :: R) (fallbackMemory I) aw rdata σ k' C' := by
  obtain ⟨aw, k', C', hr⟩ := safeRuntime_block_66_packed (by omega) h
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  simp only [safeRuntime_block_66_stack, hf] at hr
  exact ⟨aw, _, k', C', hr⟩

set_option maxRecDepth 100000 in
theorem safeFallbackReturn {I g s0 σ k C aw mem out}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨93⟩ (⟨1⟩ :: ⟨128⟩ :: R)
      mem aw out σ k C)
    (hov : R.length + 5 ≤ 1024) (hout : out.size < UInt256.size) (hm : 128 ≤ mem.size) :
    RDret fork safeBytecode g s0 σ out := by
  have hh : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat out.size).toNat ≤ out.size := by
    rw [ulit_toNat' _ hout]
    change 0 + out.size ≤ out.size
    omega
  have h102 := safeRuntime_block_93_fallthrough hov hh (by decide) h
  have hr := safeRuntime_block_102 (by omega) h102
  simpa only [safeRuntime_block_93_fallthrough_memory,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    ulit_toNat' _ hout, copyWhole_read _ _ _ hm] using hr

set_option maxRecDepth 100000 in
theorem safeFallbackRevert {I g s0 σ k C aw mem out}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨93⟩ (⟨0⟩ :: ⟨128⟩ :: R)
      mem aw out σ k C)
    (hov : R.length + 5 ≤ 1024) (hout : out.size < UInt256.size) :
    RDrev fork safeBytecode g s0 := by
  have hh : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat out.size).toNat ≤ out.size := by
    rw [ulit_toNat' _ hout]
    change 0 + out.size ≤ out.size
    omega
  have h105 := safeRuntime_block_93_taken hov hh (by decide) (by jump_dest) h
  exact safeRuntime_block_105 (by omega) h105

end Benchmarks.Safe.ViaIR
