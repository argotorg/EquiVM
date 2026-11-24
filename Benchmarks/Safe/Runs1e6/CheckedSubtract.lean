import Benchmarks.Safe.Runs1e6.Common
import Reasoning.WordArithmetic
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_017
import Benchmarks.Safe.Runs1e6.Blocks.Runtime_049

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.Runs1e6.RuntimeBlocks

namespace Benchmarks.Safe.Runs1e6

set_option maxRecDepth 100000

theorem safeSubtractTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨13886⟩ (a :: b :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hle : b.toNat ≤ a.toNat)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨0⟩ :=
    ugt_zero (by rw [usub_toNat hle]; omega)
  have h₁ := safeRuntime_block_13886_taken (by simp; omega)
    (by rw [hgt]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_3225 (by simp; omega) hret h₁
  exact ⟨_, _, h₂⟩

theorem safeSubtractUnderflow {I g s0 σ k C aw mem rdata} {a b : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨13886⟩ (a :: b :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) (hlt : a.toNat < b.toNat) : RDrev fork safeBytecode g s0 := by
  have hgt : UInt256.gt (UInt256.sub a b) a = ⟨1⟩ := by
    apply ugt_one
    rw [usub_toNat_underflow hlt]
    have := b.val.isLt
    change b.toNat < UInt256.size at this
    omega
  have h₁ := safeRuntime_block_13886_fallthrough (by omega) (by rw [hgt]; decide) h
  have h₂ := safeRuntime_block_13898
    (by simp only [safeRuntime_block_13886_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_13786
    (by simp only [safeRuntime_block_13898_stack, safeRuntime_block_13886_fallthrough_stack,
      List.length_cons]; omega) h₂

theorem safeSubtractZeroOne {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨13886⟩ (⟨0⟩ :: ⟨1⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 6 ≤ 1024) : RDrev fork safeBytecode g s0 :=
  safeSubtractUnderflow h hov (by decide)

end Benchmarks.Safe.Runs1e6
