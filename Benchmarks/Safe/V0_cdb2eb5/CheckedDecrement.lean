import Benchmarks.Safe.V0_cdb2eb5.Common
import Reasoning.WordArithmetic
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_048
import Benchmarks.Safe.V0_cdb2eb5.Blocks.Runtime_050

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V0_cdb2eb5.RuntimeBlocks

namespace Benchmarks.Safe.V0_cdb2eb5

set_option maxRecDepth 100000

theorem safeDecrementTrace {I g s0 σ k C aw mem rdata} {value ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11532⟩ (value :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hnz : value ≠ ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.sub value ⟨1⟩ :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_11532_taken (by simp; omega) hnz (by jump_dest) h
  have h₂ := safeRuntime_block_11546 (by omega) hret h₁
  simpa only [safeRuntime_block_11546_stack, lnot_zero_add] using ⟨_, _, h₂⟩

theorem safeDecrementUnderflow {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11532⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_11532_fallthrough (by omega) rfl h
  have h₂ := safeRuntime_block_11539
    (by simp only [safeRuntime_block_11532_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11010
    (by simp only [safeRuntime_block_11539_stack, safeRuntime_block_11532_fallthrough_stack,
      List.length_cons]; omega) h₂

end Benchmarks.Safe.V0_cdb2eb5
