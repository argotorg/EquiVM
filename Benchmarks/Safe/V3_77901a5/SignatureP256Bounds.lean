import Benchmarks.Safe.V3_77901a5.SignatureP256Source
import Benchmarks.Safe.V3_77901a5.BytesMemory
import Benchmarks.Safe.V3_77901a5.SafeMulTrace
import Benchmarks.Safe.V3_77901a5.SafeAddTrace
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_015
import Benchmarks.Safe.V3_77901a5.Blocks.Runtime_030

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V3_77901a5.RuntimeBlocks

namespace Benchmarks.Safe.V3_77901a5

set_option maxRecDepth 100000

theorem safeSignatureP256Bounds (p : SignatureInput)
    {I g s0 σ k C aw mem rdata src} {i s r current last : UInt256} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨2218⟩
      (i :: s :: r :: ⟨2⟩ :: current :: last :: p.required :: UInt256.ofNat src :: R)
      mem aw rdata σ k C)
    (hm : BytesMemory mem src p.signatures) (hn : p.signatures.size < UInt256.size)
    (hreq : p.requiredBytes ≤ p.signatures.size) (hov : R.length + 35 ≤ 1024) :
    (RDrev fork safeBytecode g s0 ∧
      ¬(p.requiredBytes ≤ s.toNat ∧ s.toNat + 128 ≤ p.signatures.size)) ∨
    ∃ aw' k' C', p.requiredBytes ≤ s.toNat ∧ s.toNat + 128 ≤ p.signatures.size ∧
      RD fork safeBytecode I g s0 ⟨2293⟩
        (i :: s :: r :: ⟨2⟩ :: r :: last :: p.required :: UInt256.ofNat src :: R)
        mem aw' rdata σ k' C' := by
  have hfit : p.requiredBytes < UInt256.size := lt_of_le_of_lt hreq hn
  have hmul : (UInt256.mul p.required (UInt256.ofNat 65)).toNat = p.requiredBytes := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hfit
  have h₁ := safeRuntime_block_2218 (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, h₂⟩ := safeMulTrace h₁ hfit (by simp; omega) (by jump_dest)
  by_cases hl : p.requiredBytes ≤ s.toNat
  swap
  · have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨1⟩ :=
      ult_one (by rw [hmul]; omega)
    have h₃ := safeRuntime_block_2233_fallthrough (by simp; omega)
      (by rw [hlt]; decide) h₂
    have h₄ := safeRuntime_block_2241 (by
      simp only [safeRuntime_block_2233_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₃
    exact .inl ⟨safeRuntime_block_6898 (by
      simp only [safeRuntime_block_2241_stack, safeRuntime_block_2233_fallthrough_stack,
        List.length_cons]; omega) h₄, by omega⟩
  have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨0⟩ :=
    ult_zero (by rw [hmul]; exact hl)
  have h₃ := safeRuntime_block_2233_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h₂
  have h₄ := safeRuntime_block_2257 (by simp; omega) (by jump_dest) h₃
  simp only [safeRuntime_block_2257_stack, hm.length] at h₄
  by_cases hb : s.toNat + 128 < UInt256.size
  swap
  · exact .inl ⟨safeAddOverflow h₄ (Nat.le_of_not_gt hb) (by simp; omega), by omega⟩
  obtain ⟨_, _, h₅⟩ := safeAddTrace h₄ hb (by simp; omega) (by jump_dest)
  have hadd : (s + UInt256.ofNat 128).toNat = s.toNat + 128 := addWord_toNat _ _ hb
  have hsize := ulit_toNat' p.signatures.size hn
  by_cases hh : s.toNat + 128 ≤ p.signatures.size
  · have hgt : UInt256.gt (s + UInt256.ofNat 128) (UInt256.ofNat p.signatures.size) = ⟨0⟩ :=
      ugt_zero (by rw [hadd, hsize]; exact hh)
    have h₆ := safeRuntime_block_2270_taken (by simp; omega)
      (by rw [hgt]; decide) (by jump_dest) h₅
    exact .inr ⟨_, _, _, hl, hh, h₆⟩
  · have hgt : UInt256.gt (s + UInt256.ofNat 128) (UInt256.ofNat p.signatures.size) = ⟨1⟩ :=
      ugt_one (by rw [hadd, hsize]; omega)
    have h₆ := safeRuntime_block_2270_fallthrough (by simp; omega)
      (by rw [hgt]; decide) h₅
    have h₇ := safeRuntime_block_2277 (by
      simp only [safeRuntime_block_2270_fallthrough_stack, List.length_cons]; omega)
      (by jump_dest) h₆
    exact .inl ⟨safeRuntime_block_6898 (by
      simp only [safeRuntime_block_2277_stack, safeRuntime_block_2270_fallthrough_stack,
        List.length_cons]; omega) h₇, by omega⟩

end Benchmarks.Safe.V3_77901a5
