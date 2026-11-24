import Benchmarks.Safe.ViaIR.CheckedIncrement
import Benchmarks.Safe.ViaIR.Blocks.Runtime_041
import Reasoning.WordArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 2000

theorem safeCheckedAddTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8914⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat + b.toNat < UInt256.size) (hov : R.length + 6 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have hcond : UInt256.gt a (a + b) = ⟨0⟩ := by
    rw [u256_add_comm a b]
    exact checkedAddNoOverflowGt a b hfit
  have h₁ := safeRuntime_block_8914_fallthrough (by simp; omega) hcond h
  exact ⟨_, _, safeRuntime_block_8926 (by simp; omega) hret h₁⟩

theorem safeCheckedAddOverflow {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8914⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 6 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have hcond : UInt256.gt a (a + b) = ⟨1⟩ := by
    rw [u256_add_comm a b]
    exact checkedAddOverflowGt a b hover
  have h₁ := safeRuntime_block_8914_taken (by simp; omega)
    (by rw [hcond]; decide) (by jump_dest) h
  exact safeRuntime_block_7511 (by
    simp only [safeRuntime_block_8914_taken_stack, List.length_cons]; omega) h₁

theorem safeAddTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8914⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat + b.toNat < UInt256.size) (hov : R.length + 11 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' :=
  safeCheckedAddTrace h hfit (by omega) hret

theorem safeAddOverflow {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8914⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 11 ≤ 1024) :
    RDrev fork safeBytecode g s0 :=
  safeCheckedAddOverflow h hover (by omega)

theorem safeAdd32Trace {I g s0 σ k C aw mem rdata} {a ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8900⟩ (a :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat + 32 < UInt256.size) (hov : R.length + 6 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret ((a + UInt256.ofNat 32) :: R)
      mem aw rdata σ k' C' := by
  have hcond : UInt256.gt a (a + UInt256.ofNat 32) = ⟨0⟩ := by
    rw [u256_add_comm a]
    exact checkedAddNoOverflowGt a (UInt256.ofNat 32) hfit
  have h₁ := safeRuntime_block_8900_fallthrough (by simp; omega) hcond h
  exact ⟨_, _, safeRuntime_block_8913 (by simp; omega) hret h₁⟩

theorem safeAdd32Overflow {I g s0 σ k C aw mem rdata} {a ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8900⟩ (a :: ret :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat + 32) (hov : R.length + 6 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have hcond : UInt256.gt a (a + UInt256.ofNat 32) = ⟨1⟩ := by
    rw [u256_add_comm a]
    exact checkedAddOverflowGt a (UInt256.ofNat 32) hover
  have h₁ := safeRuntime_block_8900_taken (by simp; omega)
    (by rw [hcond]; decide) (by jump_dest) h
  exact safeRuntime_block_7511 (by
    simp only [safeRuntime_block_8900_taken_stack, List.length_cons]; omega) h₁

end Benchmarks.Safe.ViaIR
