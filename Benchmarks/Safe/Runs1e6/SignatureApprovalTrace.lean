import Benchmarks.Safe.Runs1e6.SignatureApprovalSource
import Benchmarks.Safe.Runs1e6.ModuleMemory
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_014
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_015
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_030

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

def signatureApprovalMemory (mem : ByteArray) (owner hash : UInt256) : ByteArray :=
  twoWordHashMem hash (mapSlot (UInt256.land solcAddrMask owner) ⟨8⟩)
    (twoWordHashMem (UInt256.land solcAddrMask owner) ⟨8⟩ mem)

theorem safeSignatureApprovalAccept {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2348⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 2 ≤ 1024) :
    ∃ aw' k' C', RD fork safeBytecode I g s0 ⟨2949⟩ R mem aw' rdata σ k' C' := by
  have h₁ := safeRuntime_block_2348_taken hov (by decide) (by jump_dest) h
  exact safeRuntime_block_2225_packed (by omega) (by jump_dest) h₁

theorem safeSignatureApprovalReject {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2348⟩ (⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_2348_fallthrough (by omega) (by decide) h
  have h₂ := safeRuntime_block_2354 (by
    simp only [safeRuntime_block_2348_fallthrough_stack]; omega) (by jump_dest) h₁
  exact safeRuntime_block_8421 (by
    simp only [safeRuntime_block_2354_stack, safeRuntime_block_2348_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safeSignatureApprovalTrace {I g s0 σ k C aw mem rdata}
    {i s r current last required src hash executor : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2230⟩
      (i :: s :: r :: ⟨1⟩ :: current :: last :: required :: src :: hash :: executor :: R)
      mem aw rdata σ k C) (hm : 64 ≤ mem.size) (hov : R.length + 16 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬signatureApproved σ I executor r hash) ∨
    ∃ mem' aw' k' C', signatureApproved σ I executor r hash ∧
      RD fork safeBytecode I g s0 ⟨2949⟩
        (i :: s :: r :: ⟨1⟩ :: r :: last :: required :: src :: hash :: executor :: R)
        mem' aw' rdata σ k' C' ∧
      (mem' = mem ∨ mem' = signatureApprovalMemory mem r hash) := by
  have hshift : UInt256.shiftRight r ⟨0⟩ = r := by
    cases r
    simp only [UInt256.shiftRight, show ¬(0 : Fin UInt256.size) ≥ 256 by decide,
      ↓reduceIte, UInt256.mk.injEq]
    apply Fin.ext
    simp
  have h₁ := safeRuntime_block_2230_fallthrough (by simp; omega) (by decide) h
  by_cases he : UInt256.land solcAddrMask executor = UInt256.land solcAddrMask r
  · have heq : UInt256.eq (UInt256.land solcAddrMask executor)
        (UInt256.land solcAddrMask r) = ⟨1⟩ := by rw [he]; exact uInt256_eq_self _
    have h₂ := safeRuntime_block_2239_taken (by omega)
      (by rw [safeAddressMaskLiteral, hshift, heq]; decide) (by jump_dest) h₁
    simp only [safeRuntime_block_2239_taken_stack, safeAddressMaskLiteral, hshift, heq] at h₂
    obtain ⟨aw', k', C', h₃⟩ := safeSignatureApprovalAccept h₂ (by simp; omega)
    exact .inr ⟨mem, aw', k', C', .inl he, h₃, .inl rfl⟩
  have heq : UInt256.eq (UInt256.land solcAddrMask executor)
      (UInt256.land solcAddrMask r) = ⟨0⟩ := u256_eq_of_ne he
  have h₂ := safeRuntime_block_2239_fallthrough (by omega)
    (by rw [safeAddressMaskLiteral, hshift, heq]; decide) h₁
  simp only [safeRuntime_block_2239_fallthrough_stack, safeAddressMaskLiteral, hshift, heq] at h₂
  obtain ⟨aw₃, k₃, C₃, h₃⟩ := safeRuntime_block_2298_packed (by simp; omega) h₂
  have hm' : safeRuntime_block_2298_memory (mem := mem) (x5 := r) (x9 := hash) =
      signatureApprovalMemory mem r hash := by
    simp only [safeRuntime_block_2298_memory, safeAddressMaskLiteral, u256_land_comm r solcAddrMask]
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
  simp only [safeRuntime_block_2298_stack] at h₃
  rw [← safeRuntime_block_2298_memory, hm', hslot] at h₃
  change RD fork safeBytecode I g s0 ⟨2348⟩
    (UInt256.isZero (signatureApprovalWord σ I r hash) :: i :: s :: r :: ⟨1⟩ :: r :: last ::
      required :: src :: hash :: executor :: R)
    (signatureApprovalMemory mem r hash) aw₃ rdata σ k₃ C₃ at h₃
  by_cases hz : signatureApprovalWord σ I r hash = ⟨0⟩
  · rw [hz] at h₃
    exact .inl ⟨safeSignatureApprovalReject h₃ (by simp; omega),
      fun hh ↦ hh.elim he (fun hn ↦ hn hz)⟩
  rw [isZero_eq_zero_of_ne hz] at h₃
  obtain ⟨aw', k', C', h₄⟩ := safeSignatureApprovalAccept h₃ (by simp; omega)
  exact .inr ⟨_, aw', k', C', .inr hz, h₄, .inr rfl⟩

end Benchmarks.Safe.Runs1e6
