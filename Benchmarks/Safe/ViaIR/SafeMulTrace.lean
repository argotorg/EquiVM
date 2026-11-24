import Benchmarks.Safe.ViaIR.Common
import Benchmarks.Safe.ViaIR.Blocks.Runtime_036
import Benchmarks.Safe.ViaIR.Blocks.Runtime_041
import Benchmarks.Safe.ViaIR.Blocks.Runtime_043
import Benchmarks.Safe.ViaIR.Blocks.Runtime_044
import Reasoning.WordArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

private theorem safeMulFinish {I g s0 σ k C aw mem rdata} {a b n ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8870⟩
      (n :: a :: ⟨9453⟩ :: b :: n :: ret :: R) mem aw rdata σ k C)
    (ha : a ≠ ⟨0⟩) (hdiv : UInt256.div n a = b) (hov : R.length + 10 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (n :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_8870_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne ha) h
  have h₂ := safeRuntime_block_8877 (by simp; omega) (by jump_dest) h₁
  have h₃ := safeRuntime_block_9453_fallthrough (by simp; omega)
    (by rw [hdiv, u256_sub_self]; rfl) h₂
  exact ⟨_, _, safeRuntime_block_9459 (by simp; omega) hret h₃⟩

theorem safeMulTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9466⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat * b.toNat < UInt256.size) (hov : R.length + 12 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.mul a b :: R) mem aw rdata σ k' C' := by
  by_cases ha : a = ⟨0⟩
  · subst a
    have h₁ := safeRuntime_block_9466_taken (by simp; omega) (by decide) (by jump_dest) h
    have h₂ := safeRuntime_block_9496 (by simp; omega) hret h₁
    exact ⟨_, _, by simpa only [safeRuntime_block_9496_stack, u256_mul_zero_left] using h₂⟩
  · have hdiv : UInt256.div (UInt256.mul a b) a = b := by
      rw [u256_mul_comm a b]
      exact u256_mul_div_right_eq_of_noOverflow b a ha (by simpa [Nat.mul_comm] using hfit)
    have h₁ := safeRuntime_block_9466_fallthrough (by simp; omega)
      (isZero_eq_zero_of_ne ha) h
    have h₂ := safeRuntime_block_9474_fallthrough (by simp; omega)
      (by rw [hdiv, u256_sub_self]; rfl) h₁
    have h₃ := safeRuntime_block_9487 (by simp; omega) (by jump_dest) h₂
    exact safeMulFinish h₃ ha hdiv (by omega) hret

theorem safeMulOverflow {I g s0 σ k C aw mem rdata} {a b : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9466⟩ (a :: b :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat * b.toNat) (hov : R.length + 12 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have ha : a ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hover
    norm_num [UInt256.size] at hover
  have hdiv : UInt256.div (UInt256.mul a b) a ≠ b := by
    rw [u256_mul_comm a b]
    exact u256_mul_div_right_overflow_ne b a (by simpa [Nat.mul_comm] using hover)
  have h₁ := safeRuntime_block_9466_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne ha) h
  have h₂ := safeRuntime_block_9474_taken (by simp; omega)
    (u256_sub_ne_zero_of_ne hdiv.symm) (by jump_dest) h₁
  exact safeRuntime_block_7511 (by
    simp [safeRuntime_block_9474_taken_stack];
    omega) h₂

-- The IR pipeline specializes signature-length multiplication to the constant 65.
theorem safeMul65Trace {I g s0 σ k C aw mem rdata} {a ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9420⟩ (a :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat * 65 < UInt256.size) (hov : R.length + 12 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.mul a (UInt256.ofNat 65) :: R)
      mem aw rdata σ k' C' := by
  by_cases ha : a = ⟨0⟩
  · subst a
    have h₁ := safeRuntime_block_9420_taken (by simp; omega) (by decide) (by jump_dest) h
    have h₂ := safeRuntime_block_9461 (by simp; omega) hret h₁
    exact ⟨_, _, by simpa only [safeRuntime_block_9461_stack, u256_mul_zero_left] using h₂⟩
  · have hdiv : UInt256.div (UInt256.mul a (UInt256.ofNat 65)) a = UInt256.ofNat 65 := by
      rw [u256_mul_comm a]
      exact u256_mul_div_right_eq_of_noOverflow _ a ha (by change 65 * a.toNat < _; omega)
    have h₁ := safeRuntime_block_9420_fallthrough (by simp; omega)
      (isZero_eq_zero_of_ne ha) h
    have h₂ := safeRuntime_block_9427_fallthrough (by simp; omega)
      (by rw [hdiv, u256_sub_self]; rfl) h₁
    have h₃ := safeRuntime_block_9442 (by simp; omega) (by jump_dest) h₂
    exact safeMulFinish h₃ ha hdiv (by omega) hret

theorem safeMul65Overflow {I g s0 σ k C aw mem rdata} {a : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨9420⟩ (a :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat * 65) (hov : R.length + 12 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have ha : a ≠ ⟨0⟩ := by
    intro hz
    rw [hz] at hover
    norm_num [UInt256.size] at hover
  have hdiv : UInt256.div (UInt256.mul a (UInt256.ofNat 65)) a ≠ UInt256.ofNat 65 := by
    rw [u256_mul_comm a]
    exact u256_mul_div_right_overflow_ne _ a (by change _ ≤ 65 * a.toNat; omega)
  have h₁ := safeRuntime_block_9420_fallthrough (by simp; omega)
    (isZero_eq_zero_of_ne ha) h
  have h₂ := safeRuntime_block_9427_taken (by simp; omega)
    (u256_sub_ne_zero_of_ne hdiv.symm) (by jump_dest) h₁
  exact safeRuntime_block_7511 (by simp [safeRuntime_block_9427_taken_stack]; omega) h₂

end Benchmarks.Safe.ViaIR
