import Benchmarks.Safe.OwnerHeapTraces

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeCanAddOwnerCheckWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256)
    (mem : ByteArray) (hc : key.toNat < EVM.addressModulus) (hm : mem.size = 96) :
    UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_6792_taken_memory (mem := mem) (x0 := key))) σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = ownerLinkAt σ I key := by
  exact safeCanAddOwnerHeapCheckWord σ I key mem hc


theorem safeCanAddOwnerTrace {I g s0 σ k C aw mem rdata} {key ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6783⟩ (key :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (he : ownerLinkAt σ I key = ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  obtain ⟨mem', aw', k', C', hm', hr, h'⟩ := safeCanAddOwnerHeapTrace h hov hc
    (by omega) hv he hret
  exact ⟨mem', aw', k', C', hm'.trans hm, (hr 64 32 (by omega) (by omega)).trans h64, h'⟩


theorem safeCanAddOwnerTraceInvalid {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6783⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6783 (by omega) (by jump_dest) h
  exact safeInvalidOwnerTrace h₁ (by simp; omega) hc hm hv

theorem safeCanAddOwnerTraceExisting {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6783⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hv : validOwner σ I key) (he : ownerLinkAt σ I key ≠ ⟨0⟩) :
    RDrev safeBytecode g s0 := by
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
          (safeRuntime_block_8537_taken_memory (mem := mem) (x1 := prev))) σ I)) =
      UInt256.eq key (ownerLinkAt σ I prev) := by
  simp only [safeRuntime_block_8537_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hp, solcAddrMask_clean hc]
  change UInt256.eq key (UInt256.land solcAddrMask (solcSlotWordAt
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem prev ⟨2⟩ mem)) σ I)) = _
  rw [twoWordHashMemMapSlot prev ⟨2⟩ hm, u256_land_comm solcAddrMask]
  rfl

theorem safeCanRemoveOwnerTrace {I g s0 σ k C aw mem rdata} {prev key ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8528⟩ (key :: prev :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev = key)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_8528 (by simp; omega) (by jump_dest) h
  obtain ⟨mem₂, aw₂, k₂, C₂, hm₂, h64₂, h₂⟩ := safeValidOwnerTrace h₁
    (by simp; omega) hc hm hv (by jump_dest)
  have hword := safeCanRemoveOwnerCheckWord σ I prev key mem₂ hp hc hm₂
  simp only [safeRuntime_block_8537_taken_memory] at hword
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_8537_taken_packed (by simp; omega)
    (by
      have he := hword.trans (by rw [hl, uInt256_eq_self])
      exact fun hn ↦ (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (he.symm.trans hn))
    (by jump_dest) h₂
  have h₄ := safeRuntime_block_1936 (by omega) hret h₃
  simp only [safeRuntime_block_8537_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hp] at h₄
  refine ⟨twoWordHashMem prev ⟨2⟩ mem₂, aw₃, _, _,
    twoWordHashMem_size_96 prev ⟨2⟩ hm₂, ?_, h₄⟩
  exact twoWordHashMem_read64 prev ⟨2⟩ hm₂ (h64₂.trans h64)

theorem safeCanRemoveOwnerTraceInvalid {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8528⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_8528 (by omega) (by jump_dest) h
  exact safeInvalidOwnerTrace h₁ (by simp; omega) hc hm hv

theorem safeCanRemoveOwnerTraceUnlinked {I g s0 σ k C aw mem rdata} {prev key : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨8528⟩ (key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev ≠ key) :
    RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_8528 (by simp; omega) (by jump_dest) h
  obtain ⟨mem₂, aw₂, k₂, C₂, hm₂, _, h₂⟩ := safeValidOwnerTrace h₁
    (by simp; omega) hc hm hv (by jump_dest)
  have hword := safeCanRemoveOwnerCheckWord σ I prev key mem₂ hp hc hm₂
  simp only [safeRuntime_block_8537_taken_memory] at hword
  obtain ⟨_, _, h₃⟩ := safeRuntime_block_8537_fallthrough (by simp; omega)
    (hword.trans (uInt256_eq_zero_of_ne (fun he ↦ hl (uInt256_eq_one_eq he).symm))) h₂
  have h₄ := safeRuntime_block_8573 (by simp; omega) (by jump_dest) h₃
  exact safeRuntime_block_6898 (by simp; omega) h₄

end Benchmarks.Safe
