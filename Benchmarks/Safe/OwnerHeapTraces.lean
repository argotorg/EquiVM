import Benchmarks.Safe.OwnerGuards
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeCanAddOwnerHeapCheckWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256)
    (mem : ByteArray) (hc : key.toNat < EVM.addressModulus) :
    UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_6792_taken_memory (mem := mem) (x0 := key))) σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = ownerLinkAt σ I key := by
  simp only [safeRuntime_block_6792_taken_memory, safeAddressMask, solcAddrMask_clean_left hc]
  change UInt256.land (solcSlotWordAt
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key ⟨2⟩ mem)) σ I) solcAddrMask = _
  rw [twoWordHashMemMapSlotAny]
  rfl

theorem safeCanAddOwnerHeapTrace {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6783⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 96 ≤ mem.size) (hv : validOwner σ I key) (he : ownerLinkAt σ I key = ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) ∧
      RD safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_6783 (by simp; omega) (by jump_dest) h
  obtain ⟨mem₂, aw₂, k₂, C₂, hm₂, hr₂, h₂⟩ := safeValidOwnerHeapTrace h₁
    (by simp; omega) hc hm hv (by jump_dest)
  have hword := safeCanAddOwnerHeapCheckWord σ I key mem₂ hc
  simp only [safeRuntime_block_6792_taken_memory] at hword
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_6792_taken_packed (by simp; omega)
    (by
      have hz := congrArg UInt256.isZero (hword.trans he)
      exact fun hn ↦ (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hz.symm.trans hn))
    (by jump_dest) h₂
  have h₄ := safeRuntime_block_6840 (by omega) hret h₃
  simp only [safeRuntime_block_6792_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hc] at h₄
  refine ⟨twoWordHashMem key ⟨2⟩ mem₂, aw₃, _, _, ?_, ?_, h₄⟩
  · rw [twoWordHashMem_size_of_ge64 _ _ (by omega), hm₂]
  · intro off count hlo hin
    rw [twoWordHashRead _ _ _ _ _ (by omega) hlo, hr₂ off count hlo hin]

theorem safeCanAddOwnerHeapTraceExisting {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6783⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 96 ≤ mem.size) (hv : validOwner σ I key) (he : ownerLinkAt σ I key ≠ ⟨0⟩) :
    RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6783 (by omega) (by jump_dest) h
  obtain ⟨mem₂, aw₂, k₂, C₂, hm₂, _, h₂⟩ := safeValidOwnerHeapTrace h₁
    (by simp; omega) hc hm hv (by jump_dest)
  have hword := safeCanAddOwnerHeapCheckWord σ I key mem₂ hc
  simp only [safeRuntime_block_6792_taken_memory] at hword
  obtain ⟨_, _, h₃⟩ := safeRuntime_block_6792_fallthrough (by omega)
    (isZero_eq_zero_of_ne (fun hz ↦ he (hword.symm.trans hz))) h₂
  have h₄ := safeRuntime_block_6824 (by simp; omega) (by jump_dest) h₃
  exact safeRuntime_block_6898 (by simp; omega) h₄

end Benchmarks.Safe
