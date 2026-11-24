import Benchmarks.Safe.ViaIR.SignatureOwnerSource
import Benchmarks.Safe.ViaIR.Blocks.Runtime_038

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeSignatureOwnerReject {I g s0 σ k C aw mem rdata scratch} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7836⟩ (scratch :: ⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_7836_taken (by simp; omega) (by decide) (by jump_dest) h
  exact safeRuntime_block_7852 (by simp [safeRuntime_block_7836_taken_stack]; omega) h₁

theorem safeSignatureOwnerTrace {I g s0 σ k C aw mem rdata i}
    {src hash current last : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7803⟩
      (last :: current :: src :: hash :: UInt256.ofNat i :: R) mem aw rdata σ k C)
    (hm : 64 ≤ mem.size) (hov : R.length + 13 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬signatureOwnerValid σ I current last) ∨
    ∃ aw' k' C', signatureOwnerValid σ I current last ∧
      RD fork safeBytecode I g s0 ⟨7553⟩
        (current :: src :: hash :: UInt256.ofNat (i + 1) :: R)
        (twoWordHashMem (UInt256.land solcAddrMask current) ⟨2⟩ mem) aw' rdata σ k' C' := by
  by_cases hgt : (UInt256.land solcAddrMask last).toNat <
      (UInt256.land solcAddrMask current).toNat
  swap
  · have hg : UInt256.gt (UInt256.land solcAddrMask current)
        (UInt256.land solcAddrMask last) = ⟨0⟩ := ugt_zero (by omega)
    have h₁ := safeRuntime_block_7803_fallthrough (by simp; omega)
      (by rw [safeAddressMask, u256_land_comm current solcAddrMask]; exact hg) h
    simp only [safeRuntime_block_7803_fallthrough_stack, safeAddressMask,
      u256_land_comm current solcAddrMask, hg] at h₁
    have h₂ := safeRuntime_block_7829_fallthrough (by simp; omega) (by decide) h₁
    exact .inl ⟨safeSignatureOwnerReject h₂ (by simp; omega), fun hh ↦ hgt hh.1⟩
  have hg : UInt256.gt (UInt256.land solcAddrMask current)
      (UInt256.land solcAddrMask last) = ⟨1⟩ := ugt_one hgt
  have h₁ := safeRuntime_block_7803_taken (by simp; omega)
    (by rw [safeAddressMask, u256_land_comm current solcAddrMask, hg]; decide)
    (by jump_dest) h
  obtain ⟨aw₂, k₂, C₂, h₂⟩ := safeRuntime_block_7908_packed (by simp; omega)
    (by jump_dest) h₁
  have hmem : safeRuntime_block_7908_memory
      (mem := mem) (x0 := UInt256.land current solcAddrMask) =
      twoWordHashMem (UInt256.land solcAddrMask current) ⟨2⟩ mem := by
    simp only [safeRuntime_block_7908_memory, u256_land_comm current solcAddrMask]
    rfl
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64)
      (twoWordHashMem (UInt256.land solcAddrMask current) ⟨2⟩ mem) =
      mapSlot (UInt256.land solcAddrMask current) ⟨2⟩ :=
    twoWordHashMem_mapSlot_of_ge64 _ _ hm
  simp only [safeRuntime_block_7908_stack, safeAddressMask] at h₂
  rw [← safeRuntime_block_7908_memory, hmem, hslot,
    u256_land_comm current solcAddrMask] at h₂
  have hload : UInt256.land solcAddrMask
      (σ.get? I.codeOwner |>.option (⟨0⟩ : UInt256) (fun ac ↦
        ac.storage.getD (mapSlot (UInt256.land solcAddrMask current) ⟨2⟩) ⟨0⟩)) =
      ownerLinkAt σ I (UInt256.land solcAddrMask current) := u256_land_comm _ _
  rw [hload] at h₂
  change RD fork safeBytecode I g s0 ⟨7829⟩
    (UInt256.land solcAddrMask current ::
      UInt256.isZero (ownerLinkAt σ I (UInt256.land solcAddrMask current)) ::
      current :: src :: hash :: UInt256.ofNat i :: R)
    (twoWordHashMem (UInt256.land solcAddrMask current) ⟨2⟩ mem) aw₂ rdata σ k₂ C₂ at h₂
  by_cases howner : ownerLinkAt σ I (UInt256.land solcAddrMask current) = ⟨0⟩
  · rw [howner] at h₂
    have h₃ := safeRuntime_block_7829_fallthrough (by simp; omega) (by decide) h₂
    exact .inl ⟨safeSignatureOwnerReject h₃ (by simp; omega), fun hh ↦ hh.2.1 howner⟩
  rw [isZero_eq_zero_of_ne howner] at h₂
  have h₃ := safeRuntime_block_7829_taken (by simp; omega) (by decide) (by jump_dest) h₂
  have h₄ := safeRuntime_block_7897 (by simp; omega) (by jump_dest) h₃
  simp only [safeRuntime_block_7897_stack] at h₄
  by_cases hone : UInt256.land solcAddrMask current = ⟨1⟩
  · rw [hone] at h₄
    exact .inl ⟨safeSignatureOwnerReject h₄ (by simp; omega), fun hh ↦ hh.2.2 hone⟩
  have he : UInt256.eq (UInt256.land solcAddrMask current) (UInt256.ofNat 1) = ⟨0⟩ :=
    u256_eq_of_ne hone
  rw [he] at h₄
  have h₅ := safeRuntime_block_7836_fallthrough (by simp; omega) rfl h₄
  obtain ⟨aw', k', C', h₆⟩ := safeRuntime_block_7842_packed (by simp; omega) (by jump_dest) h₅
  refine .inr ⟨aw', k', C', ⟨hgt, howner, hone⟩, ?_⟩
  have hinc : UInt256.ofNat i + UInt256.ofNat 1 = UInt256.ofNat (i + 1) := by
    rw [u256_add_comm]; exact u256_one_add_ofNat i
  simpa only [safeRuntime_block_7842_stack, hinc] using h₆

end Benchmarks.Safe.ViaIR
