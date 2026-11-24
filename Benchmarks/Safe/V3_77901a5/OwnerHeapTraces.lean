import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_013
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_029
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_030
import Benchmarks.Safe.V3_77901a5.OwnerGuards
import Benchmarks.Safe.V3_77901a5.MemoryPreserves

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V3_77901a5.RuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

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

theorem safeCanAddOwnerCallTrace {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6783⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 64 ≤ mem.size) (hv : validOwner σ I key) (he : ownerLinkAt σ I key = ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) ∧
      RD fork safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_6783 (by simp; omega) (by jump_dest) h
  obtain ⟨mem₁, aw₁, _, _, hm₁, hr, h₂⟩ := safeValidOwnerTrace h₁ (by simp; omega)
    hc (by omega) hv (by jump_dest)
  have hword := safeCanAddOwnerHeapCheckWord σ I key mem₁ hc
  simp only [safeRuntime_block_6792_taken_memory] at hword
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_6792_taken_packed (by simp; omega)
    (by
      have hz := congrArg UInt256.isZero (hword.trans he)
      exact fun hn ↦ (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hz.symm.trans hn)) (by jump_dest) h₂
  simp only [safeRuntime_block_6792_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hc] at h₃
  have h₄ := safeRuntime_block_6840 (by simp; omega) hret h₃
  refine ⟨twoWordHashMem key ⟨2⟩ mem₁, aw₃, _, _, ?_, ?_, h₄⟩
  · exact (twoWordHashMem_size_of_ge64 _ _ (by omega)).trans hm₁
  · intro off count hlo hin
    exact (twoWordHashRead _ _ _ _ _ (by omega) hlo).trans (hr off count (by omega) hin)

theorem safeCanAddOwnerCallTraceInvalid {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6783⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6783 (by simp; omega) (by jump_dest) h
  exact safeInvalidOwnerTrace h₁ (by simp; omega) hc hm hv

theorem safeCanAddOwnerCallTraceExisting {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6783⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : validOwner σ I key) (he : ownerLinkAt σ I key ≠ ⟨0⟩) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6783 (by simp; omega) (by jump_dest) h
  obtain ⟨mem₁, _, _, _, _, _, h₂⟩ := safeValidOwnerTrace h₁ (by simp; omega)
    hc hm hv (by jump_dest)
  have hword := safeCanAddOwnerHeapCheckWord σ I key mem₁ hc
  simp only [safeRuntime_block_6792_taken_memory] at hword
  obtain ⟨_, _, h₃⟩ := safeRuntime_block_6792_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne (fun hz ↦ he (hword.symm.trans hz))) h₂
  have h₄ := safeRuntime_block_6824 (by simp; omega) (by jump_dest) h₃
  exact safeRuntime_block_6898 (by simp; omega) h₄

theorem safeCanAddOwnerHeapTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 96 ≤ mem.size) (hv : validOwner σ I key) (he : ownerLinkAt σ I key = ⟨0⟩) :
    ∃ mem' aw' k' C', mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) ∧
      RD fork safeBytecode I g s0 ⟨1753⟩ (top :: key :: R) mem' aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_1744 (by simp; omega) (by jump_dest) h
  exact safeCanAddOwnerCallTrace h₁ (by simp; omega) hc (by omega) hv he (by jump_dest)

theorem safeCanAddOwnerHeapTraceExisting {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 96 ≤ mem.size) (hv : validOwner σ I key) (he : ownerLinkAt σ I key ≠ ⟨0⟩) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_1744 (by simp; omega) (by jump_dest) h
  exact safeCanAddOwnerCallTraceExisting h₁ (by simp; omega) hc (by omega) hv he

end Benchmarks.Safe.V3_77901a5
