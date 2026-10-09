import Benchmarks.Safe.FallbackMemory
import Benchmarks.Safe.ByteCopy

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

theorem safeFallbackPrepare {I g s0 σ k C rdata}
    {handler : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨588⟩ (handler :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata σ k C)
    (hov : R.length + 9 ≤ 1024) :
    ∃ aw gasArg k' C', RD safeBytecode I g s0 ⟨614⟩
      (gasArg :: handler :: ⟨0⟩ :: ⟨128⟩ ::
        (UInt256.ofNat I.calldata.size + UInt256.ofNat 20) :: ⟨0⟩ :: ⟨0⟩ ::
        ⟨128⟩ :: handler :: R) (fallbackMemory I) aw rdata σ k' C' := by
  obtain ⟨aw, k', C', hr⟩ := safeRuntime_block_588_packed hov h
  have hf : memLoad (UInt256.ofNat 64) solcFreePtrMem = ⟨128⟩ := solcFreePtrMem_mload64
  simp only [safeRuntime_block_588_stack, hf] at hr
  exact ⟨aw, _, k', C', hr⟩

set_option maxRecDepth 100000 in
theorem safeFallbackReturn {I g s0 σ k C aw mem out}
    {handler : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨615⟩ (⟨1⟩ :: ⟨128⟩ :: handler :: R)
      mem aw out σ k C)
    (hov : R.length + 5 ≤ 1024) (hout : out.size < UInt256.size) (hm : 128 ≤ mem.size) :
    RDret safeBytecode g s0 σ out := by
  have hh : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat out.size).toNat ≤ out.size := by
    rw [ulit_toNat' _ hout]
    change 0 + out.size ≤ out.size
    omega
  have h629 := safeRuntime_block_615_taken hov hh (by decide) (by jump_dest) h
  have hr := safeRuntime_block_629 (by
    simp only [safeRuntime_block_615_taken_stack, List.length_cons]
    omega) h629
  simpa only [safeRuntime_block_615_taken_memory,
    show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    show (⟨128⟩ : UInt256).toNat = 128 from rfl,
    ulit_toNat' _ hout, copyWhole_read _ _ _ hm] using hr

theorem safeFallbackRevert {I g s0 σ k C aw mem out}
    {handler : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨615⟩ (⟨0⟩ :: ⟨128⟩ :: handler :: R)
      mem aw out σ k C)
    (hov : R.length + 5 ≤ 1024) (hout : out.size < UInt256.size) :
    RDrev safeBytecode g s0 := by
  have hh : (⟨0⟩ : UInt256).toNat + (UInt256.ofNat out.size).toNat ≤ out.size := by
    rw [ulit_toNat' _ hout]
    change 0 + out.size ≤ out.size
    omega
  have h626 := safeRuntime_block_615_fallthrough hov hh rfl h
  exact safeRuntime_block_626 (by
    simp only [safeRuntime_block_615_fallthrough_stack, List.length_cons]
    omega) h626

end Benchmarks.Safe
