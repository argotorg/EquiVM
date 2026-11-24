import Benchmarks.Safe.V0_cdb2eb5.SafeAddTrace
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_017
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_030
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_048
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_049
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_050

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem safeCheckedMulTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11553⟩ (b :: a :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat * b.toNat < UInt256.size) (hov : R.length + 7 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.mul a b :: R) mem aw rdata σ k' C' := by
  have hg : UInt256.lor (UInt256.eq a (UInt256.div (UInt256.mul a b) b))
      (UInt256.isZero b) ≠ UInt256.ofNat 0 := by
    by_cases hb : b = ⟨0⟩
    · rw [hb]
      change UInt256.lor _ ⟨1⟩ ≠ ⟨0⟩
      rw [u256_lor_comm]
      exact u256_lor_one_ne_zero _
    · rw [u256_mul_div_right_eq_of_noOverflow a b hb hfit, u256_eq_refl]
      exact u256_lor_one_ne_zero _
  have h₁ := safeRuntime_block_11553_taken (by simp; omega) hg (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_2759 (by omega) hret h₁⟩

theorem safeCheckedMulOverflow {I g s0 σ k C aw mem rdata} {a b : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11553⟩ (b :: a :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat) (hov : R.length + 7 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have hb : b ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hover
    norm_num [UInt256.size] at hover
  have hg : UInt256.lor (UInt256.eq a (UInt256.div (UInt256.mul a b) b))
      (UInt256.isZero b) = UInt256.ofNat 0 := by
    have hne := u256_mul_div_right_overflow_ne a b hover
    rw [u256_eq_of_ne (Ne.symm hne), isZero_eq_zero_of_ne hb]
    decide
  have h₁ := safeRuntime_block_11553_fallthrough (by omega) hg h
  have h₂ := safeRuntime_block_11569 (by
    simp only [safeRuntime_block_11553_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11010 (by
    simp only [safeRuntime_block_11569_stack, safeRuntime_block_11553_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safeMulTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7027⟩ (b :: a :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat * b.toNat < UInt256.size) (hov : R.length + 12 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.mul a b :: R) mem aw rdata σ k' C' := by
  by_cases ha : a = ⟨0⟩
  · subst a
    have h₁ := safeRuntime_block_7027_fallthrough (by simp; omega) (by decide) h
    have h₂ := safeRuntime_block_7036 (by simp; omega) (by jump_dest) h₁
    have h₃ := safeRuntime_block_2759 (by omega) hret h₂
    exact ⟨_, _, by simpa only [safeRuntime_block_2759_stack, u256_mul_zero_left] using h₃⟩
  · have h₁ := safeRuntime_block_7027_taken (by simp; omega)
      (u256_zero_sub_ne_zero ha) (by jump_dest) h
    have h₂ := safeRuntime_block_7042 (by simp; omega) (by jump_dest) h₁
    obtain ⟨_, _, h₃⟩ := safeCheckedMulTrace h₂ (by simpa [Nat.mul_comm] using hfit)
      (by simp; omega) (by jump_dest)
    have h₄ := safeRuntime_block_7053 (by simp; omega) (by jump_dest) h₃
    have h₅ := safeRuntime_block_11343_taken (by simp; omega) ha (by jump_dest) h₄
    have h₆ := safeRuntime_block_11369 (by simp; omega) (by jump_dest) h₅
    have hdiv : UInt256.div (UInt256.mul b a) a = b :=
      u256_mul_div_right_eq_of_noOverflow b a ha (by simpa [Nat.mul_comm] using hfit)
    have h₇ := safeRuntime_block_7066_taken (by simp; omega)
      (by rw [hdiv, u256_eq_refl]; decide) (by jump_dest) h₆
    have h₈ := safeRuntime_block_7075 (by omega) hret h₇
    exact ⟨_, _, by simpa only [safeRuntime_block_7075_stack, u256_mul_comm b a] using h₈⟩

theorem safeMulOverflow {I g s0 σ k C aw mem rdata} {a b : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨7027⟩ (b :: a :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat) (hov : R.length + 12 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have ha : a ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hover
    norm_num [UInt256.size] at hover
  have h₁ := safeRuntime_block_7027_taken (by omega)
    (u256_zero_sub_ne_zero ha) (by jump_dest) h
  have h₂ := safeRuntime_block_7042 (by omega) (by jump_dest) h₁
  exact safeCheckedMulOverflow h₂ (by simpa [Nat.mul_comm] using hover) (by simp; omega)

end Benchmarks.Safe.V0_cdb2eb5
