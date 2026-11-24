import Benchmarks.Safe.Runs1e6.ContractSignatureCheckSource
import Benchmarks.Safe.Runs1e6.BytesMemory
import Benchmarks.Safe.Runs1e6.SafeAddTrace

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

open ContractSignatureInput

set_option maxRecDepth 100000

theorem safeCheckContractBounds (p : ContractSignatureInput)
    {I g s0 σ k C aw mem rdata src} {owner ret : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8484⟩
      (p.offset :: UInt256.ofNat src :: p.hash :: owner :: ret :: R) mem aw rdata σ k C)
    (hm : BytesMemory mem src p.signatures)
    (hb : src + 64 + p.signatures.size < UInt256.size) (hov : R.length + 20 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧ ¬(p.start ≤ p.signatures.size ∧ p.finish ≤ p.signatures.size)) ∨
      ∃ aw' k' C', p.start ≤ p.signatures.size ∧ p.finish ≤ p.signatures.size ∧
        RD fork safeBytecode I g s0 ⟨8633⟩
          (p.len :: p.offset :: UInt256.ofNat src :: p.hash :: owner :: ret :: R)
          mem aw' rdata σ k' C' := by
  have hlen := hm.length
  have h₁ := safeRuntime_block_8484 (by simp; omega) (by jump_dest) h
  simp only [safeRuntime_block_8484_stack, hlen] at h₁
  by_cases hsfit : p.start < UInt256.size
  swap
  · exact Or.inl ⟨safeAddOverflow h₁ (Nat.le_of_not_gt hsfit) (by simp; omega), by omega⟩
  obtain ⟨_, _, h₂⟩ := safeAddTrace h₁ hsfit (by simp; omega) (by jump_dest)
  have hstart : (p.offset + UInt256.ofNat 32).toNat = p.start :=
    addWord_toNat _ _ hsfit
  have hn : (UInt256.ofNat p.signatures.size).toNat = p.signatures.size :=
    ulit_toNat' _ (by omega)
  by_cases hs : p.start ≤ p.signatures.size
  swap
  · have hcond : UInt256.gt (p.offset + UInt256.ofNat 32)
        (UInt256.ofNat p.signatures.size) = ⟨1⟩ := ugt_one (by rw [hstart, hn]; omega)
    have h₃ := safeRuntime_block_8497_fallthrough (by simp; omega)
      (by rw [hcond]; decide) h₂
    have h₄ := safeRuntime_block_8504 (by
      simp only [safeRuntime_block_8497_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact Or.inl ⟨safeRuntime_block_8421 (by
      simp only [safeRuntime_block_8504_stack, safeRuntime_block_8497_fallthrough_stack,
        List.length_cons]; omega) h₄, by omega⟩
  have hcond : UInt256.gt (p.offset + UInt256.ofNat 32)
      (UInt256.ofNat p.signatures.size) = ⟨0⟩ := ugt_zero (by rw [hstart, hn]; exact hs)
  have h₃ := safeRuntime_block_8497_taken (by simp; omega)
    (by rw [hcond]; decide) (by jump_dest) h₂
  have hread : memLoad ((UInt256.ofNat src + p.offset) + UInt256.ofNat 32) mem = p.len := by
    have haddr : (UInt256.ofNat src + p.offset) + UInt256.ofNat 32 =
        UInt256.ofNat (src + 32 + p.offset.toNat) := by
      apply u256_inj
      change ((src % UInt256.size + p.offset.toNat) % UInt256.size + 32) % UInt256.size =
        (src + 32 + p.offset.toNat) % UInt256.size
      have hs' : p.offset.toNat + 32 ≤ p.signatures.size := hs
      rw [Nat.mod_eq_of_lt (by omega : src < UInt256.size),
        Nat.mod_eq_of_lt (by omega : src + p.offset.toNat < UInt256.size)]
      congr 1
      omega
    rw [haddr]
    exact hm.word hs (by have hs' : p.offset.toNat + 32 ≤ p.signatures.size := hs; omega)
  have h₄ := safeRuntime_block_8544 (by simp; omega) (by jump_dest) h₃
  change RD fork safeBytecode I g s0 ⟨8703⟩ _ _ _ _ _ _ _ at h₄
  simp only [safeRuntime_block_8544_stack, hread, hlen] at h₄
  obtain ⟨_, _, h₅⟩ := safeAddTrace h₄ hsfit (by simp; omega) (by jump_dest)
  have h₆ := safeRuntime_block_8580 (by simp; omega) (by jump_dest) h₅
  by_cases hefit : p.finish < UInt256.size
  swap
  · exact Or.inl ⟨safeAddOverflow h₆ (by rw [hstart]; exact Nat.le_of_not_gt hefit)
      (by simp; omega), by omega⟩
  obtain ⟨_, _, h₇⟩ := safeAddTrace h₆ (by rw [hstart]; exact hefit)
    (by simp; omega) (by jump_dest)
  have hend : (p.offset + UInt256.ofNat 32 + p.len).toNat = p.finish := by
    have he := addWord_toNat (p.offset + UInt256.ofNat 32) p.len
      (by rw [hstart]; exact hefit)
    simpa only [hstart] using he
  by_cases he : p.finish ≤ p.signatures.size
  · have hcond : UInt256.gt (p.offset + UInt256.ofNat 32 + p.len)
        (UInt256.ofNat p.signatures.size) = ⟨0⟩ := ugt_zero (by rw [hend, hn]; exact he)
    have h₈ := safeRuntime_block_8586_taken (by simp; omega)
      (by rw [hcond]; decide) (by jump_dest) h₇
    exact Or.inr ⟨_, _, _, hs, he, h₈⟩
  · have hcond : UInt256.gt (p.offset + UInt256.ofNat 32 + p.len)
        (UInt256.ofNat p.signatures.size) = ⟨1⟩ := ugt_one (by rw [hend, hn]; omega)
    have h₈ := safeRuntime_block_8586_fallthrough (by simp; omega)
      (by rw [hcond]; decide) h₇
    have h₉ := safeRuntime_block_8593 (by
      simp only [safeRuntime_block_8586_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₈
    exact Or.inl ⟨safeRuntime_block_8421 (by
      simp only [safeRuntime_block_8593_stack, safeRuntime_block_8586_fallthrough_stack,
        List.length_cons]; omega) h₉, by omega⟩

end Benchmarks.Safe.Runs1e6
