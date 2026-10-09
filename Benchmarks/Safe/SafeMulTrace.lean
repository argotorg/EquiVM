import Benchmarks.Safe.SafeAddTrace
import Benchmarks.Safe.Blocks.Runtime_029
import Benchmarks.Safe.Blocks.Runtime_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeCheckedMulTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11684⟩ (b :: a :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat * b.toNat < UInt256.size) (hov : R.length + 7 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (UInt256.mul a b :: R) mem aw rdata σ k' C' := by
  have hg : UInt256.lor (UInt256.eq a (UInt256.div (UInt256.mul a b) b))
      (UInt256.isZero b) ≠ UInt256.ofNat 0 := by
    by_cases hb : b = ⟨0⟩
    · rw [hb]
      change UInt256.lor _ ⟨1⟩ ≠ ⟨0⟩
      rw [u256_lor_comm]
      exact u256_lor_one_ne_zero _
    · rw [u256_mul_div_right_eq_of_noOverflow a b hb hfit, u256_eq_refl]
      exact u256_lor_one_ne_zero _
  have h₁ := safeRuntime_block_11684_taken (by simp; omega) hg (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_2853 (by omega) hret h₁⟩

theorem safeCheckedMulOverflow {I g s0 σ k C aw mem rdata} {a b : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11684⟩ (b :: a :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat) (hov : R.length + 7 ≤ 1024) :
    RDrev safeBytecode g s0 := by
  have hb : b ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hover
    norm_num [UInt256.size] at hover
  have hg : UInt256.lor (UInt256.eq a (UInt256.div (UInt256.mul a b) b))
      (UInt256.isZero b) = UInt256.ofNat 0 := by
    have hne := u256_mul_div_right_overflow_ne a b hover
    rw [u256_eq_of_ne (Ne.symm hne), isZero_eq_zero_of_ne hb]
    decide
  have h₁ := safeRuntime_block_11684_fallthrough (by omega) hg h
  have h₂ := safeRuntime_block_11700 (by
    simp only [safeRuntime_block_11684_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11141 (by
    simp only [safeRuntime_block_11700_stack, safeRuntime_block_11684_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safeMulTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6843⟩ (b :: a :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat * b.toNat < UInt256.size) (hov : R.length + 12 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (UInt256.mul a b :: R) mem aw rdata σ k' C' := by
  by_cases ha : a = ⟨0⟩
  · subst a
    have h₁ := safeRuntime_block_6843_fallthrough (by simp; omega) (by decide) h
    have h₂ := safeRuntime_block_6852 (by simp; omega) (by jump_dest) h₁
    have h₃ := safeRuntime_block_2853 (by omega) hret h₂
    exact ⟨_, _, by simpa only [safeRuntime_block_2853_stack, u256_mul_zero_left] using h₃⟩
  · have h₁ := safeRuntime_block_6843_taken (by simp; omega)
      (u256_zero_sub_ne_zero ha) (by jump_dest) h
    have h₂ := safeRuntime_block_6858 (by simp; omega) (by jump_dest) h₁
    obtain ⟨_, _, h₃⟩ := safeCheckedMulTrace h₂ (by simpa [Nat.mul_comm] using hfit)
      (by simp; omega) (by jump_dest)
    have h₄ := safeRuntime_block_6869 (by simp; omega) (by jump_dest) h₃
    have h₅ := safeRuntime_block_11474_taken (by simp; omega) ha (by jump_dest) h₄
    have h₆ := safeRuntime_block_11500 (by simp; omega) (by jump_dest) h₅
    have hdiv : UInt256.div (UInt256.mul b a) a = b :=
      u256_mul_div_right_eq_of_noOverflow b a ha (by simpa [Nat.mul_comm] using hfit)
    have h₇ := safeRuntime_block_6882_taken (by simp; omega)
      (by rw [hdiv, u256_eq_refl]; decide) (by jump_dest) h₆
    have h₈ := safeRuntime_block_6891 (by omega) hret h₇
    exact ⟨_, _, by simpa only [safeRuntime_block_6891_stack, u256_mul_comm b a] using h₈⟩

theorem safeMulOverflow {I g s0 σ k C aw mem rdata} {a b : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨6843⟩ (b :: a :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat) (hov : R.length + 12 ≤ 1024) :
    RDrev safeBytecode g s0 := by
  have ha : a ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hover
    norm_num [UInt256.size] at hover
  have h₁ := safeRuntime_block_6843_taken (by omega)
    (u256_zero_sub_ne_zero ha) (by jump_dest) h
  have h₂ := safeRuntime_block_6858 (by omega) (by jump_dest) h₁
  exact safeCheckedMulOverflow h₂ (by simpa [Nat.mul_comm] using hover) (by simp; omega)

end Benchmarks.Safe
