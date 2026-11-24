import Benchmarks.Safe.V0_cdb2eb5.ModulesGuards
import Benchmarks.Safe.V0_cdb2eb5.AddressArrayMemory
import Benchmarks.Safe.V0_cdb2eb5.Memory
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_024

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 2000

theorem safeModulesAllocate {I g s0 σ k C aw mem rdata n start} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨4802⟩
      (⟨0⟩ :: ⟨96⟩ :: UInt256.ofNat n :: start :: R) mem aw rdata σ k C)
    (hov : R.length + 11 ≤ 1024) (hn : n ≤ 2 ^ 64 - 1) (hz : n ≠ 0)
    (hc : start.toNat < EVM.addressModulus) (hsize : I.calldata.size < UInt256.size)
    (hm : mem.size = 96) (hread : mem.readWithPadding 64 32 = (⟨128⟩ : UInt256).toByteArray) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨4901⟩
      (⟨0⟩ :: moduleLinkAt σ I start :: ⟨128⟩ :: UInt256.ofNat n :: start :: R)
      (twoWordHashMem start ⟨1⟩ (addressArrayAllocatedMemory mem n)) aw' rdata σ k' C' := by
  have hnword := ulit_toNat' n (by change n < 2 ^ 256; omega)
  have hgt : UInt256.gt (UInt256.ofNat n)
      (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 64))
        (UInt256.ofNat 1)) = ⟨0⟩ := ugt_zero (by simpa only [hnword] using hn)
  have h₁ := safeRuntime_block_4802_taken (by simp; omega)
    (by rw [hgt]; decide) (by jump_dest) h
  have hfree : memLoad (UInt256.ofNat 64) mem = ⟨128⟩ := memLoad_of_wordRead _ _ _ hread
  have hnz : UInt256.ofNat n ≠ ⟨0⟩ := by
    intro he
    have hv := congrArg UInt256.toNat he
    exact hz (hnword.symm.trans hv)
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_4826_fallthrough_packed
    (by simp only [safeRuntime_block_4802_taken_stack, List.length_cons]; omega)
    (isZero_eq_zero_of_ne hnz) h₁
  have halloc : safeRuntime_block_4826_fallthrough_memory (mem := mem) (x0 := UInt256.ofNat n) =
      addressArrayAllocatedMemory mem n := by
    simp only [safeRuntime_block_4826_fallthrough_memory, hfree, addressArrayFreePtr_eq n hn]
    rfl
  simp only [safeRuntime_block_4826_fallthrough_stack, hfree, halloc] at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_4852_packed (by simp; omega) h₂
  have hcopy : safeRuntime_block_4852_memory (ee := I)
      (mem := addressArrayAllocatedMemory mem n) (x0 := UInt256.ofNat n) (x1 := ⟨128⟩) =
      addressArrayAllocatedMemory mem n := by
    simp only [safeRuntime_block_4852_memory, ulit_toNat' _ hsize]
    change I.calldata.write I.calldata.size (addressArrayAllocatedMemory mem n) 160 _ = _
    rw [← safeAddressArrayAllocatedSize mem n hm]
    exact writePastSourceAtMemoryEnd _ _ _
  rw [hcopy] at h₃
  obtain ⟨aw₄, k₄, C₄, h₄⟩ := safeRuntime_block_4867_packed
    (by omega) h₃
  simp only [safeRuntime_block_4867_stack, safeRuntime_block_4867_memory,
    safeAddressMask, solcAddrMask_clean hc] at h₄
  have hh := twoWordHashMem_mapSlot_of_ge64 (mem := addressArrayAllocatedMemory mem n)
    start ⟨1⟩ (by rw [safeAddressArrayAllocatedSize mem n hm]; decide)
  change keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem start ⟨1⟩ (addressArrayAllocatedMemory mem n)) =
    mapSlot start ⟨1⟩ at hh
  change RD fork safeBytecode I g s0 ⟨4901⟩
    (⟨0⟩ :: UInt256.land (solcSlotWordAt
      (keccakWord ⟨0⟩ ⟨64⟩ (twoWordHashMem start ⟨1⟩ (addressArrayAllocatedMemory mem n)))
      σ I) solcAddrMask :: ⟨128⟩ :: UInt256.ofNat n :: start :: R)
    (twoWordHashMem start ⟨1⟩ (addressArrayAllocatedMemory mem n)) aw₄ rdata σ k₄ C₄ at h₄
  rw [hh] at h₄
  exact ⟨aw₄, k₄, C₄, h₄⟩

end Benchmarks.Safe.V0_cdb2eb5
