import Benchmarks.Safe.V0_cdb2eb5.CheckedIncrement
import Reasoning.WordArithmetic
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_017
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_031
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_038
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_048
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_049

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem safeCheckedAddTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11324⟩ (b :: a :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat + b.toNat < UInt256.size) (hov : R.length + 6 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_11324_taken (by simp; omega)
    (by rw [checkedAddNoOverflowGt b a (by omega)]; decide) (by jump_dest) h
  exact ⟨_, _, safeRuntime_block_2759 (by omega) hret h₁⟩

theorem safeCheckedAddOverflow {I g s0 σ k C aw mem rdata} {a b : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11324⟩ (b :: a :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 6 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_11324_fallthrough (by omega)
    (by rw [checkedAddOverflowGt b a (by omega)]; decide) h
  have h₂ := safeRuntime_block_11336 (by
    simp only [safeRuntime_block_11324_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11010 (by
    simp only [safeRuntime_block_11336_stack, safeRuntime_block_11324_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safeAddTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8786⟩ (b :: a :: ret :: R) mem aw rdata σ k C)
    (hfit : a.toNat + b.toNat < UInt256.size) (hov : R.length + 11 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret ((a + b) :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_8786 (by simp; omega) (by jump_dest) h
  obtain ⟨_, _, h₂⟩ := safeCheckedAddTrace h₁ (by omega) (by simp; omega) (by jump_dest)
  have hlt : UInt256.lt (b + a) a = ⟨0⟩ := by
    apply ult_zero
    have hadd : (b + a).toNat = b.toNat + a.toNat := addWord_toNat b a (by omega)
    rw [hadd]
    omega
  have h₃ := safeRuntime_block_8798_taken (by simp; omega)
    (by rw [hlt]; decide) (by jump_dest) h₂
  have h₄ := safeRuntime_block_7075 (by omega) hret h₃
  exact ⟨_, _, by simpa only [safeRuntime_block_7075_stack, u256_add_comm b a] using h₄⟩

theorem safeAddOverflow {I g s0 σ k C aw mem rdata} {a b : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨8786⟩ (b :: a :: R) mem aw rdata σ k C)
    (hover : UInt256.size ≤ a.toNat + b.toNat) (hov : R.length + 11 ≤ 1024) :
    RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_8786 (by omega) (by jump_dest) h
  exact safeCheckedAddOverflow h₁ (by omega) (by simp; omega)

end Benchmarks.Safe.V0_cdb2eb5
