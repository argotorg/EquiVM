import Benchmarks.Safe.V0_cdb2eb5.SignatureOwnerSource
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_016
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_030

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem safeSignatureOwnerReject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2661⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_2661_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_2667 (by
    simp only [safeRuntime_block_2661_fallthrough_stack]; omega) (by jump_dest) h₁
  exact safeRuntime_block_6990 (by
    simp only [safeRuntime_block_2667_stack, safeRuntime_block_2661_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safeSignatureOwnerTrace {I g s0 σ k C aw mem rdata i}
    {s r v current last : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2585⟩
      (UInt256.ofNat i :: s :: r :: v :: current :: last :: R) mem aw rdata σ k C)
    (hm : 64 ≤ mem.size) (hi : i + 1 < UInt256.size) (hov : R.length + 13 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬signatureOwnerValid σ I current last) ∨
    ∃ aw' k' C', signatureOwnerValid σ I current last ∧
      RD fork safeBytecode I g s0 ⟨2094⟩
        (UInt256.ofNat (i + 1) :: s :: r :: v :: current :: current :: R)
        (twoWordHashMem (UInt256.land solcAddrMask current) ⟨2⟩ mem) aw' rdata σ k' C' := by
  by_cases hgt : (UInt256.land solcAddrMask last).toNat <
      (UInt256.land solcAddrMask current).toNat
  swap
  · have hg : UInt256.gt (UInt256.land solcAddrMask current)
        (UInt256.land solcAddrMask last) = ⟨0⟩ := ugt_zero (by omega)
    have h₁ := safeRuntime_block_2585_taken (by omega)
      (by rw [safeAddressMask, hg]; decide) (by jump_dest) h
    simp only [safeRuntime_block_2585_taken_stack, safeAddressMask, hg] at h₁
    have h₂ := safeRuntime_block_2641_taken (by simp; omega) (by decide) (by jump_dest) h₁
    exact .inl ⟨safeSignatureOwnerReject h₂ (by simp; omega), fun hh ↦ hgt hh.1⟩
  have hg : UInt256.gt (UInt256.land solcAddrMask current)
      (UInt256.land solcAddrMask last) = ⟨1⟩ := ugt_one hgt
  have h₁ := safeRuntime_block_2585_fallthrough (by omega)
    (by rw [safeAddressMask, hg]; decide) h
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_2613_packed (by simp; omega) h₁
  have hmem : safeRuntime_block_2613_memory (mem := mem) (x5 := current) =
      twoWordHashMem (UInt256.land solcAddrMask current) ⟨2⟩ mem := by
    simp only [safeRuntime_block_2613_memory, safeAddressMask]
    rfl
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.land solcAddrMask current) ⟨2⟩ mem) =
      mapSlot (UInt256.land solcAddrMask current) ⟨2⟩ :=
    twoWordHashMem_mapSlot_of_ge64 _ _ hm
  simp only [safeRuntime_block_2613_stack] at h₂
  rw [← safeRuntime_block_2613_memory, hmem, hslot, safeAddressMask] at h₂
  change RD fork safeBytecode I g s0 ⟨2641⟩
    (UInt256.isZero (ownerLinkAt σ I (UInt256.land solcAddrMask current)) ::
      UInt256.ofNat i :: s :: r :: v :: current :: last :: R)
    (twoWordHashMem (UInt256.land solcAddrMask current) ⟨2⟩ mem) aw₂ rdata σ k₂ C₂ at h₂
  by_cases howner : ownerLinkAt σ I (UInt256.land solcAddrMask current) = ⟨0⟩
  · rw [howner] at h₂
    have h₃ := safeRuntime_block_2641_taken (by simp; omega) (by decide) (by jump_dest) h₂
    exact .inl ⟨safeSignatureOwnerReject h₃ (by simp; omega), fun hh ↦ hh.2.1 howner⟩
  rw [isZero_eq_zero_of_ne howner] at h₂
  have h₃ := safeRuntime_block_2641_fallthrough (by simp; omega) rfl h₂
  have h₄ := safeRuntime_block_2647 (by simp; omega) h₃
  simp only [safeRuntime_block_2647_stack, safeAddressMask,
    u256_land_comm current solcAddrMask] at h₄
  by_cases hone : UInt256.land solcAddrMask current = ⟨1⟩
  · rw [hone] at h₄
    exact .inl ⟨safeSignatureOwnerReject h₄ (by simp; omega), fun hh ↦ hh.2.2 hone⟩
  have he : UInt256.eq (UInt256.ofNat 1) (UInt256.land solcAddrMask current) = ⟨0⟩ :=
    u256_eq_of_ne (Ne.symm hone)
  rw [he] at h₄
  have h₅ := safeRuntime_block_2661_taken (by simp; omega) (by decide) (by jump_dest) h₄
  obtain ⟨aw', k', C', h₆⟩ := safeRuntime_block_2683_packed (by omega) (by jump_dest) h₅
  refine .inr ⟨aw', k', C', ⟨hgt, howner, hone⟩, ?_⟩
  have hinc : UInt256.ofNat 1 + UInt256.ofNat i = UInt256.ofNat (i + 1) :=
    u256_one_add_ofNat i
  simpa only [safeRuntime_block_2683_stack, hinc] using h₆

end Benchmarks.Safe.V0_cdb2eb5
