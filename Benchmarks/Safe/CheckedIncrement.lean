import Benchmarks.Safe.Common
import Benchmarks.Safe.Blocks.Runtime_049

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeIncrementTrace {I g s0 σ k C aw mem rdata} {value ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11161⟩ (value :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hno : value.toNat + 1 < UInt256.size)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret ((value + ⟨1⟩) :: R) mem aw rdata σ k' C' := by
  have hn : value + UInt256.ofNat 1 ≠ ⟨0⟩ := by
    intro hz
    have hv := congrArg UInt256.toNat hz
    rw [uadd_word_ofNat_toNat value 1 hno] at hv
    change value.toNat + 1 = 0 at hv
    omega
  have h₁ := safeRuntime_block_11161_taken (by simp; omega) hn (by jump_dest) h
  have h₂ := safeRuntime_block_11178 (by omega) hret h₁
  simp only [safeRuntime_block_11178_stack] at h₂
  have he : UInt256.ofNat 1 + value = value + (⟨1⟩ : UInt256) := by
    apply u256_inj
    rw [uadd_toNat, uadd_toNat, Nat.add_comm]
    rfl
  rw [he] at h₂
  exact ⟨_, _, h₂⟩

theorem safeIncrementOverflow {I g s0 σ k C aw mem rdata} {value : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11161⟩ (value :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hno : ¬value.toNat + 1 < UInt256.size) :
    RDrev safeBytecode g s0 := by
  have hn : value + UInt256.ofNat 1 = ⟨0⟩ := by
    apply u256_inj
    change (value.toNat + 1) % UInt256.size = 0
    have hv : value.toNat < UInt256.size := value.val.isLt
    have he : value.toNat + 1 = UInt256.size := by omega
    rw [he, Nat.mod_self]
  have h₁ := safeRuntime_block_11161_fallthrough (by omega) hn h
  have h₂ := safeRuntime_block_11171
    (by simp only [safeRuntime_block_11161_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11141
    (by simp only [safeRuntime_block_11171_stack, safeRuntime_block_11161_fallthrough_stack,
      List.length_cons]; omega) h₂

end Benchmarks.Safe
