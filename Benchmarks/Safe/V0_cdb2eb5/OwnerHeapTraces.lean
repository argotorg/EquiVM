import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_030
import Benchmarks.Safe.V0_cdb2eb5.OwnerGuards
import Benchmarks.Safe.V0_cdb2eb5.MemoryPreserves
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_014

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem safeCanAddOwnerHeapCheckWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256)
    (mem : ByteArray) (hc : key.toNat < EVM.addressModulus) :
    UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_1797_taken_memory (mem := mem) (x1 := key))) σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = ownerLinkAt σ I key := by
  simp only [safeRuntime_block_1797_taken_memory, safeAddressMask, solcAddrMask_clean_left hc]
  change UInt256.land (solcSlotWordAt
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem key ⟨2⟩ mem)) σ I) solcAddrMask = _
  rw [twoWordHashMemMapSlotAny]
  rfl

theorem safeCanAddOwnerHeapTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 96 ≤ mem.size) (hv : validOwner σ I key) (he : ownerLinkAt σ I key = ⟨0⟩) :
    ∃ mem' aw' k' C', mem'.size = mem.size ∧
      (∀ off count, 64 ≤ off → off + count ≤ mem.size →
        mem'.readWithPadding off count = mem.readWithPadding off count) ∧
      RD fork safeBytecode I g s0 ⟨1845⟩ (top :: key :: R) mem' aw' rdata σ k' C' := by
  obtain ⟨_, _, h₂⟩ := safeValidOwnerTrace h (by omega) hc hv
  have hword := safeCanAddOwnerHeapCheckWord σ I key mem hc
  simp only [safeRuntime_block_1797_taken_memory] at hword
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_1797_taken_packed (by omega)
    (by
      have hz := congrArg UInt256.isZero (hword.trans he)
      exact fun hn ↦ (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hz.symm.trans hn)) (by jump_dest) h₂
  simp only [safeRuntime_block_1797_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hc] at h₃
  refine ⟨twoWordHashMem key ⟨2⟩ mem, aw₃, k₃, C₃, ?_, ?_, h₃⟩
  · exact twoWordHashMem_size_of_ge64 _ _ (by omega)
  · intro off count hlo hin
    exact twoWordHashRead _ _ _ _ _ hin hlo

theorem safeCanAddOwnerHeapTraceExisting {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 96 ≤ mem.size) (hv : validOwner σ I key) (he : ownerLinkAt σ I key ≠ ⟨0⟩) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h₂⟩ := safeValidOwnerTrace h (by omega) hc hv
  have hword := safeCanAddOwnerHeapCheckWord σ I key mem hc
  simp only [safeRuntime_block_1797_taken_memory] at hword
  obtain ⟨_, _, h₃⟩ := safeRuntime_block_1797_fallthrough (by omega)
    (isZero_eq_zero_of_ne (fun hz ↦ he (hword.symm.trans hz))) h₂
  have h₄ := safeRuntime_block_1829 (by simp; omega) (by jump_dest) h₃
  exact safeRuntime_block_6990 (by simp; omega) h₄

end Benchmarks.Safe.V0_cdb2eb5
