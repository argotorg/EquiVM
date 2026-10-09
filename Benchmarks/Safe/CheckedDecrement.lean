import Benchmarks.Safe.Common
import Reasoning.WordArithmetic
import Benchmarks.Safe.Blocks.Runtime_049
import Benchmarks.Safe.Blocks.Runtime_051

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000

theorem safeDecrementTrace {I g s0 σ k C aw mem rdata} {value ret : UInt256}
    {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11663⟩ (value :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hnz : value ≠ ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (UInt256.sub value ⟨1⟩ :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_11663_taken (by simp; omega) hnz (by jump_dest) h
  have h₂ := safeRuntime_block_11677 (by omega) hret h₁
  simpa only [safeRuntime_block_11677_stack, lnot_zero_add] using ⟨_, _, h₂⟩

theorem safeDecrementUnderflow {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨11663⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) : RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_11663_fallthrough (by omega) rfl h
  have h₂ := safeRuntime_block_11670
    (by simp only [safeRuntime_block_11663_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_11141
    (by simp only [safeRuntime_block_11670_stack, safeRuntime_block_11663_fallthrough_stack,
      List.length_cons]; omega) h₂

end Benchmarks.Safe
