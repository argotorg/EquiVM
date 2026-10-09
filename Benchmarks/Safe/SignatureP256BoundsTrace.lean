import Benchmarks.Safe.SignatureP256BoundsSource
import Benchmarks.Safe.BytesMemory
import Benchmarks.Safe.SafeMulTrace
import Benchmarks.Safe.SafeAddTrace
import Benchmarks.Safe.Blocks.Runtime_015

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeSignatureP256Bounds (p : SignatureInput)
    {I g s0 σ k C aw mem rdata src} {i s r v current last : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨2218⟩
      (i :: s :: r :: v :: current :: last :: p.required :: UInt256.ofNat src :: R)
      mem aw rdata σ k C)
    (hm : BytesMemory mem src p.signatures) (hn : p.signatures.size < UInt256.size)
    (hreq : p.requiredBytes ≤ p.signatures.size) (hov : R.length + 21 ≤ 1024) :
    (RDrev safeBytecode g s0 ∧
      ¬(p.requiredBytes ≤ s.toNat ∧ s.toNat + 128 ≤ p.signatures.size)) ∨
    ∃ aw' k' C', p.requiredBytes ≤ s.toNat ∧ s.toNat + 128 ≤ p.signatures.size ∧
      RD safeBytecode I g s0 ⟨2293⟩
        (i :: s :: r :: v :: r :: last :: p.required :: UInt256.ofNat src :: R)
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
        List.length_cons]; omega) h₄, fun hh ↦ hl hh.1⟩
  have hlt : UInt256.lt s (UInt256.mul p.required (UInt256.ofNat 65)) = ⟨0⟩ :=
    ult_zero (by rw [hmul]; exact hl)
  have h₃ := safeRuntime_block_2233_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h₂
  have h₄ := safeRuntime_block_2257 (by simp; omega) (by jump_dest) h₃
  by_cases hb : s.toNat + 128 < UInt256.size
  swap
  · exact .inl ⟨safeAddOverflow h₄ (by
      change UInt256.size ≤ s.toNat + 128; omega) (by simp; omega), fun hh ↦ hb (by omega)⟩
  obtain ⟨_, _, h₅⟩ := safeAddTrace h₄ hb (by simp; omega) (by jump_dest)
  have hsum : (s + UInt256.ofNat 128).toNat = s.toNat + 128 := addWord_toNat _ _ hb
  by_cases hh : s.toNat + 128 ≤ p.signatures.size
  · have hgt : UInt256.gt (s + UInt256.ofNat 128) (memLoad (UInt256.ofNat src) mem) = ⟨0⟩ :=
      ugt_zero (by rw [hm.length, ulit_toNat' _ hn, hsum]; exact hh)
    have h₆ := safeRuntime_block_2270_taken (by simp; omega)
      (by rw [hgt]; decide) (by jump_dest) h₅
    exact .inr ⟨_, _, _, hl, hh, h₆⟩
  · have hgt : UInt256.gt (s + UInt256.ofNat 128) (memLoad (UInt256.ofNat src) mem) = ⟨1⟩ :=
      ugt_one (by rw [hm.length, ulit_toNat' _ hn, hsum]; omega)
    have h₆ := safeRuntime_block_2270_fallthrough (by simp; omega) (by rw [hgt]; decide) h₅
    have h₇ := safeRuntime_block_2277 (by
      simp only [safeRuntime_block_2270_fallthrough_stack]; simp; omega) (by jump_dest) h₆
    exact .inl ⟨safeRuntime_block_6898 (by
      simp only [safeRuntime_block_2277_stack, safeRuntime_block_2270_fallthrough_stack,
        List.length_cons]; omega) h₇, fun hbad ↦ hh hbad.2⟩

end Benchmarks.Safe
