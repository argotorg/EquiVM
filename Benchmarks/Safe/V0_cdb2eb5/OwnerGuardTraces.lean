import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_028
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_029
import Benchmarks.Safe.V0_cdb2eb5.OwnerHeapTraces
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_014
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_030
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_038

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem safeCanAddOwnerCheckWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256)
    (mem : ByteArray) (hc : key.toNat < EVM.addressModulus) (hm : mem.size = 96) :
    UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_1797_taken_memory (mem := mem) (x1 := key))) σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = ownerLinkAt σ I key := by
  exact safeCanAddOwnerHeapCheckWord σ I key mem hc


theorem safeCanAddOwnerTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (he : ownerLinkAt σ I key = ⟨0⟩)
    :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ⟨1845⟩ (top :: key :: R) mem' aw' rdata σ k' C' := by
  obtain ⟨mem', aw', k', C', hm', hr, h'⟩ := safeCanAddOwnerHeapTrace h hov hc
    (by omega) hv he
  exact ⟨mem', aw', k', C', hm'.trans hm, (hr 64 32 (by omega) (by omega)).trans h64, h'⟩


theorem safeCanAddOwnerTraceInvalid {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  exact safeInvalidOwnerTrace h (by omega) hc hv

theorem safeCanAddOwnerTraceExisting {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hv : validOwner σ I key) (he : ownerLinkAt σ I key ≠ ⟨0⟩) :
    RDrev fork safeBytecode g s0 := by
  exact safeCanAddOwnerHeapTraceExisting h hov hc (by omega) hv he


theorem safeCanRemoveOwnerCheckWord (σ : AccountMap) (I : ExecutionEnv)
    (prev key : UInt256) (mem : ByteArray)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) :
    UInt256.eq (UInt256.land key
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)))
      (UInt256.land
        (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
          (UInt256.ofNat 1))
        (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
          (safeRuntime_block_6782_taken_memory (mem := mem) (x2 := prev))) σ I)) =
      UInt256.eq key (ownerLinkAt σ I prev) := by
  simp only [safeRuntime_block_6782_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hp, solcAddrMask_clean hc]
  change UInt256.eq key (UInt256.land solcAddrMask (solcSlotWordAt
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem prev ⟨2⟩ mem)) σ I)) = _
  rw [twoWordHashMemMapSlot prev ⟨2⟩ hm, u256_land_comm solcAddrMask]
  rfl

theorem safeCanRemoveOwnerTrace {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6729⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev = key)
    :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ⟨6834⟩ (top :: key :: prev :: R) mem' aw' rdata σ k' C' := by
  obtain ⟨_, _, h₂⟩ := safeValidRemoveOwnerTrace h (by simp; omega) hc hv
  have hword := safeCanRemoveOwnerCheckWord σ I prev key mem hp hc hm
  simp only [safeRuntime_block_6782_taken_memory] at hword
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_6782_taken_packed (by simp; omega)
    (by
      have he := hword.trans (by rw [hl, uInt256_eq_self])
      exact fun hn ↦ (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (he.symm.trans hn))
    (by jump_dest) h₂
  simp only [safeRuntime_block_6782_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hp] at h₃
  refine ⟨twoWordHashMem prev ⟨2⟩ mem, aw₃, _, _,
    twoWordHashMem_size_96 prev ⟨2⟩ hm, ?_, h₃⟩
  exact twoWordHashMem_read64 prev ⟨2⟩ hm h64

theorem safeCanRemoveOwnerTraceInvalid {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6729⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  exact safeInvalidRemoveOwnerTrace h (by omega) hc hv

theorem safeCanRemoveOwnerTraceUnlinked {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6729⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev ≠ key) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h₂⟩ := safeValidRemoveOwnerTrace h (by simp; omega) hc hv
  have hword := safeCanRemoveOwnerCheckWord σ I prev key mem hp hc hm
  simp only [safeRuntime_block_6782_taken_memory] at hword
  obtain ⟨_, _, h₃⟩ := safeRuntime_block_6782_fallthrough (by simp; omega)
    (hword.trans (uInt256_eq_zero_of_ne (fun he ↦ hl (uInt256_eq_one_eq he).symm))) h₂
  have h₄ := safeRuntime_block_6818 (by simp; omega) (by jump_dest) h₃
  exact safeRuntime_block_6990 (by simp; omega) h₄
theorem safeSwapCanRemoveOwnerTrace {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6282⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev = key)
    :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ⟨6387⟩ (top :: key :: prev :: R) mem' aw' rdata σ k' C' := by
  obtain ⟨_, _, h₂⟩ := safeValidSwapOldOwnerTrace h (by simp; omega) hc hv
  have hword := safeCanRemoveOwnerCheckWord σ I prev key mem hp hc hm
  simp only [safeRuntime_block_6782_taken_memory] at hword
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_6335_taken_packed (by simp; omega)
    (by
      have he := hword.trans (by rw [hl, uInt256_eq_self])
      exact fun hn ↦ (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (he.symm.trans hn))
    (by jump_dest) h₂
  simp only [safeRuntime_block_6335_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hp] at h₃
  refine ⟨twoWordHashMem prev ⟨2⟩ mem, aw₃, _, _,
    twoWordHashMem_size_96 prev ⟨2⟩ hm, ?_, h₃⟩
  exact twoWordHashMem_read64 prev ⟨2⟩ hm h64

theorem safeSwapCanRemoveOwnerTraceInvalid {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6282⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  exact safeInvalidSwapOldOwnerTrace h (by omega) hc hv

theorem safeSwapCanRemoveOwnerTraceUnlinked {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6282⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev ≠ key) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h₂⟩ := safeValidSwapOldOwnerTrace h (by simp; omega) hc hv
  have hword := safeCanRemoveOwnerCheckWord σ I prev key mem hp hc hm
  simp only [safeRuntime_block_6782_taken_memory] at hword
  obtain ⟨_, _, h₃⟩ := safeRuntime_block_6335_fallthrough (by simp; omega)
    (hword.trans (uInt256_eq_zero_of_ne (fun he ↦ hl (uInt256_eq_one_eq he).symm))) h₂
  have h₄ := safeRuntime_block_6371 (by simp; omega) (by jump_dest) h₃
  exact safeRuntime_block_6990 (by simp; omega) h₄

theorem safeSwapCanAddOwnerTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6162⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (hself : key ≠ UInt256.ofNat I.codeOwner.val)
    (he : ownerLinkAt σ I key = ⟨0⟩) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ⟨6282⟩ (key :: R) mem' aw' rdata σ k' C' := by
  obtain ⟨_, _, h₂⟩ := safeValidSwapNewOwnerTrace h (by omega) hc hv hself
  have hword := safeCanAddOwnerHeapCheckWord σ I key mem hc
  simp only [safeRuntime_block_1797_taken_memory] at hword
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_6234_taken_packed (by omega)
    (by
      have hz := congrArg UInt256.isZero (hword.trans he)
      exact fun hn ↦ (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (hz.symm.trans hn)) (by jump_dest) h₂
  simp only [safeRuntime_block_6234_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hc] at h₃
  exact ⟨twoWordHashMem key ⟨2⟩ mem, aw₃, k₃, C₃,
    twoWordHashMem_size_96 _ _ hm, twoWordHashMem_read64 _ _ hm h64, h₃⟩

theorem safeSwapCanAddOwnerTraceExisting {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6162⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hv : validOwner σ I key) (hself : key ≠ UInt256.ofNat I.codeOwner.val)
    (he : ownerLinkAt σ I key ≠ ⟨0⟩) : RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h₂⟩ := safeValidSwapNewOwnerTrace h (by omega) hc hv hself
  have hword := safeCanAddOwnerHeapCheckWord σ I key mem hc
  simp only [safeRuntime_block_1797_taken_memory] at hword
  obtain ⟨_, _, h₃⟩ := safeRuntime_block_6234_fallthrough (by omega)
    (isZero_eq_zero_of_ne (fun hz ↦ he (hword.symm.trans hz))) h₂
  have h₄ := safeRuntime_block_6266 (by simp; omega) (by jump_dest) h₃
  exact safeRuntime_block_6990 (by simp; omega) h₄

end Benchmarks.Safe.V0_cdb2eb5
