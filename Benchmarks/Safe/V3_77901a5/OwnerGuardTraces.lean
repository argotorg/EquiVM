import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_013
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_014
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_028
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_029
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_030
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_037
import Benchmarks.Safe.V3_77901a5.OwnerHeapTraces

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V3_77901a5.RuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000

theorem safeCanAddOwnerCheckWord (σ : AccountMap) (I : ExecutionEnv) (key : UInt256)
    (mem : ByteArray) (hc : key.toNat < EVM.addressModulus) (hm : mem.size = 96) :
    UInt256.land (solcSlotWordAt (keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (safeRuntime_block_6792_taken_memory (mem := mem) (x0 := key))) σ I)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1)) = ownerLinkAt σ I key := by
  exact safeCanAddOwnerHeapCheckWord σ I key mem hc


theorem safeCanAddOwnerTrace {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (he : ownerLinkAt σ I key = ⟨0⟩)
    :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ⟨1753⟩ (top :: key :: R) mem' aw' rdata σ k' C' := by
  obtain ⟨mem', aw', k', C', hm', hr, h'⟩ := safeCanAddOwnerHeapTrace h hov hc
    (by omega) hv he
  exact ⟨mem', aw', k', C', hm'.trans hm, (hr 64 32 (by omega) (by omega)).trans h64, h'⟩


theorem safeCanAddOwnerTraceInvalid {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_1744 (by simp; omega) (by jump_dest) h
  exact safeCanAddOwnerCallTraceInvalid h₁ (by simp; omega) hc hm hv

theorem safeCanAddOwnerTraceExisting {I g s0 σ k C aw mem rdata} {key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨1744⟩ (top :: key :: R) mem aw rdata σ k C)
    (hov : R.length + 12 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
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
          (safeRuntime_block_8537_taken_memory (mem := mem) (x1 := prev))) σ I)) =
      UInt256.eq key (ownerLinkAt σ I prev) := by
  simp only [safeRuntime_block_8537_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hp, solcAddrMask_clean hc]
  change UInt256.eq key (UInt256.land solcAddrMask (solcSlotWordAt
    (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem prev ⟨2⟩ mem)) σ I)) = _
  rw [twoWordHashMemMapSlot prev ⟨2⟩ hm, u256_land_comm solcAddrMask]
  rfl

theorem safeCanRemoveOwnerCallTrace {I g s0 σ k C aw mem rdata} {prev key ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8528⟩ (key :: prev :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev = key)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ret R mem' aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_8528 (by simp; omega) (by jump_dest) h
  obtain ⟨mem₁, aw₁, _, _, hm₁, hr, h₂⟩ := safeValidOwnerTrace h₁ (by simp; omega)
    hc (by omega) hv (by jump_dest)
  have hm₁' := hm₁.trans hm
  have h64₁ := (hr 64 32 (by omega) (by omega)).trans h64
  have hword := safeCanRemoveOwnerCheckWord σ I prev key mem₁ hp hc hm₁'
  simp only [safeRuntime_block_8537_taken_memory] at hword
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_8537_taken_packed (by simp; omega)
    (by
      have he := hword.trans (by rw [hl, uInt256_eq_self])
      exact fun hn ↦ (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) (he.symm.trans hn))
    (by jump_dest) h₂
  simp only [safeRuntime_block_8537_taken_memory, safeAddressMask,
    solcAddrMask_clean_left hp] at h₃
  have h₄ := safeRuntime_block_1936 (by simp; omega) hret h₃
  exact ⟨twoWordHashMem prev ⟨2⟩ mem₁, aw₃, _, _,
    twoWordHashMem_size_96 prev ⟨2⟩ hm₁', twoWordHashMem_read64 prev ⟨2⟩ hm₁' h64₁, h₄⟩

theorem safeCanRemoveOwnerCallTraceInvalid {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8528⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 9 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_8528 (by simp; omega) (by jump_dest) h
  exact safeInvalidOwnerTrace h₁ (by simp; omega) hc hm hv

theorem safeCanRemoveOwnerCallTraceUnlinked {I g s0 σ k C aw mem rdata} {prev key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8528⟩ (key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 10 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev ≠ key) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_8528 (by simp; omega) (by jump_dest) h
  obtain ⟨mem₁, _, _, _, hm₁, _, h₂⟩ := safeValidOwnerTrace h₁ (by simp; omega)
    hc (by omega) hv (by jump_dest)
  have hword := safeCanRemoveOwnerCheckWord σ I prev key mem₁ hp hc (hm₁.trans hm)
  simp only [safeRuntime_block_8537_taken_memory] at hword
  obtain ⟨_, _, h₃⟩ := safeRuntime_block_8537_fallthrough (by simp; omega)
    (hword.trans (uInt256_eq_zero_of_ne (fun he ↦ hl (uInt256_eq_one_eq he).symm))) h₂
  have h₄ := safeRuntime_block_8573 (by simp; omega) (by jump_dest) h₃
  exact safeRuntime_block_6898 (by simp; omega) h₄

theorem safeCanRemoveOwnerTrace {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6617⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev = key)
    :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ⟨6627⟩ (top :: key :: prev :: R) mem' aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_6617 (by simp; omega) (by jump_dest) h
  exact safeCanRemoveOwnerCallTrace h₁ (by simp; omega) hp hc hm h64 hv hl (by jump_dest)


theorem safeCanRemoveOwnerTraceInvalid {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6617⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6617 (by simp; omega) (by jump_dest) h
  exact safeCanRemoveOwnerCallTraceInvalid h₁ (by simp; omega) hc hm hv


theorem safeCanRemoveOwnerTraceUnlinked {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6617⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev ≠ key) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6617 (by simp; omega) (by jump_dest) h
  exact safeCanRemoveOwnerCallTraceUnlinked h₁ (by simp; omega) hp hc hm hv hl


theorem safeSwapCanRemoveOwnerTrace {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6265⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev = key)
    :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ⟨6275⟩ (top :: key :: prev :: R) mem' aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_6265 (by simp; omega) (by jump_dest) h
  exact safeCanRemoveOwnerCallTrace h₁ (by simp; omega) hp hc hm h64 hv hl (by jump_dest)


theorem safeSwapCanRemoveOwnerTraceInvalid {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6265⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6265 (by simp; omega) (by jump_dest) h
  exact safeCanRemoveOwnerCallTraceInvalid h₁ (by simp; omega) hc hm hv


theorem safeSwapCanRemoveOwnerTraceUnlinked {I g s0 σ k C aw mem rdata} {prev key top : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6265⟩ (top :: key :: prev :: R) mem aw rdata σ k C)
    (hov : R.length + 14 ≤ 1024)
    (hp : prev.toNat < EVM.addressModulus) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (hv : validOwner σ I key) (hl : ownerLinkAt σ I prev ≠ key) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6265 (by simp; omega) (by jump_dest) h
  exact safeCanRemoveOwnerCallTraceUnlinked h₁ (by simp; omega) hp hc hm hv hl


theorem safeSwapCanAddOwnerTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6256⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : mem.size = 96) (h64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hv : validOwner σ I key)
    (he : ownerLinkAt σ I key = ⟨0⟩) :
    ∃ mem' aw' k' C', mem'.size = 96 ∧
      mem'.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ ∧
      RD fork safeBytecode I g s0 ⟨6265⟩ (key :: R) mem' aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_6256 (by simp; omega) (by jump_dest) h
  obtain ⟨mem', aw', k', C', hm', hr, h'⟩ := safeCanAddOwnerCallTrace h₁
    (by simp; omega) hc (by omega) hv he (by jump_dest)
  exact ⟨mem', aw', k', C', hm'.trans hm, (hr 64 32 (by omega) (by omega)).trans h64, h'⟩


theorem safeSwapCanAddOwnerTraceExisting {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6256⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : validOwner σ I key)
    (he : ownerLinkAt σ I key ≠ ⟨0⟩) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6256 (by simp; omega) (by jump_dest) h
  exact safeCanAddOwnerCallTraceExisting h₁ (by simp; omega) hc hm hv he


theorem safeInvalidSwapNewOwnerTrace {I g s0 σ k C aw mem rdata} {key : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨6256⟩ (key :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hc : key.toNat < EVM.addressModulus)
    (hm : 32 ≤ mem.size) (hv : ¬validOwner σ I key) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_6256 (by simp; omega) (by jump_dest) h
  exact safeCanAddOwnerCallTraceInvalid h₁ (by simp; omega) hc hm hv

end Benchmarks.Safe.V3_77901a5
