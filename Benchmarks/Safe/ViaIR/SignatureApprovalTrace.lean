import Benchmarks.Safe.ViaIR.SignatureApprovalSource
import Benchmarks.Safe.ViaIR.Blocks.Runtime_039

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

def signatureApprovalMemory (mem : ByteArray) (owner hash : UInt256) : ByteArray :=
  twoWordHashMem hash (mapSlot (UInt256.land solcAddrMask owner) ⟨8⟩)
    (twoWordHashMem (UInt256.land solcAddrMask owner) ⟨8⟩ mem)

theorem safeSignatureApprovalAccept {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8171⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨7803⟩ R mem aw' rdata σ k' C' := by
  exact safeRuntime_block_8171_taken_packed hov (by decide) (by jump_dest) h

theorem safeSignatureApprovalReject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8171⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_8171_fallthrough (by omega) (by decide) h
  exact safeRuntime_block_8177 (by simp [safeRuntime_block_8171_fallthrough_stack]; omega) h₁

theorem safeSignatureApprovalTrace {I g s0 σ k C aw mem rdata}
    {i s r last required src hash executor : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8128⟩
      (⟨1⟩ :: r :: s :: r :: last :: s :: src :: hash :: i :: executor :: required :: R)
      mem aw rdata σ k C) (hm : 64 ≤ mem.size) (hov : R.length + 16 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬signatureApproved σ I executor r hash) ∨
    ∃ mem' aw' k' C', signatureApproved σ I executor r hash ∧
      RD fork safeBytecode I g s0 ⟨7803⟩
        (last :: UInt256.land solcAddrMask r :: src :: hash :: i :: executor :: required :: R)
        mem' aw' rdata σ k' C' ∧
      (mem' = mem ∨ mem' = signatureApprovalMemory mem r hash) := by
  have h₁ := safeRuntime_block_8128_fallthrough (by simp; omega) (by decide) h
  by_cases he : UInt256.land solcAddrMask executor = UInt256.land solcAddrMask r
  · have heq : UInt256.eq (UInt256.land solcAddrMask r)
        (UInt256.land solcAddrMask executor) = ⟨1⟩ := by rw [he]; exact uInt256_eq_self _
    have h₂ := safeRuntime_block_8145_fallthrough (by simp; omega)
      (by rw [safeAddressMask, u256_land_comm executor solcAddrMask, heq]; decide) h₁
    simp only [safeRuntime_block_8145_fallthrough_stack, safeAddressMask,
      u256_land_comm executor solcAddrMask, heq] at h₂
    obtain ⟨aw', k', C', h₃⟩ := safeSignatureApprovalAccept h₂ (by simp; omega)
    exact .inr ⟨mem, aw', k', C', .inl he, h₃, .inl rfl⟩
  have heq : UInt256.eq (UInt256.land solcAddrMask r)
      (UInt256.land solcAddrMask executor) = ⟨0⟩ := u256_eq_of_ne (Ne.symm he)
  have h₂ := safeRuntime_block_8145_taken (by simp; omega)
    (by rw [safeAddressMask, u256_land_comm executor solcAddrMask, heq]; decide)
    (by jump_dest) h₁
  simp only [safeRuntime_block_8145_taken_stack, safeAddressMask,
    u256_land_comm executor solcAddrMask, heq] at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_8221_packed (by simp; omega) (by jump_dest) h₂
  have hm' : safeRuntime_block_8221_memory
      (mem := mem) (x2 := UInt256.land solcAddrMask r) (x4 := hash) =
      signatureApprovalMemory mem r hash := by
    simp only [safeRuntime_block_8221_memory]
    change twoWordHashMem hash
      (keccakWord ⟨0⟩ (UInt256.ofNat 64) (twoWordHashMem (UInt256.land solcAddrMask r) ⟨8⟩ mem))
      (twoWordHashMem (UInt256.land solcAddrMask r) ⟨8⟩ mem) = _
    have hk : keccakWord ⟨0⟩ (UInt256.ofNat 64)
        (twoWordHashMem (UInt256.land solcAddrMask r) ⟨8⟩ mem) =
        mapSlot (UInt256.land solcAddrMask r) ⟨8⟩ :=
      twoWordHashMem_mapSlot_of_ge64 _ _ hm
    rw [hk]
    rfl
  have hslot : keccakWord ⟨0⟩ (UInt256.ofNat 64) (signatureApprovalMemory mem r hash) =
      mapSlot hash (mapSlot (UInt256.land solcAddrMask r) ⟨8⟩) := by
    exact twoWordHashMem_mapSlot_of_ge64 _ _ (by
      rw [twoWordHashMem_size_of_ge64 _ _ hm]; exact hm)
  simp only [safeRuntime_block_8221_stack] at h₃
  rw [← safeRuntime_block_8221_memory, hm', hslot] at h₃
  change RD fork safeBytecode I g s0 ⟨8171⟩
    (UInt256.isZero (signatureApprovalWord σ I r hash) :: last :: UInt256.land solcAddrMask r ::
      src :: hash :: i :: executor :: required :: R)
    (signatureApprovalMemory mem r hash) aw₃ rdata σ k₃ C₃ at h₃
  by_cases hz : signatureApprovalWord σ I r hash = ⟨0⟩
  · rw [hz] at h₃
    exact .inl ⟨safeSignatureApprovalReject h₃ (by simp; omega),
      fun hh ↦ hh.elim he (fun hn ↦ hn hz)⟩
  rw [isZero_eq_zero_of_ne hz] at h₃
  obtain ⟨aw', k', C', h₄⟩ := safeSignatureApprovalAccept h₃ (by simp; omega)
  exact .inr ⟨_, aw', k', C', .inr hz, h₄, .inr rfl⟩

end Benchmarks.Safe.ViaIR
