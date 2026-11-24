import Benchmarks.Safe.V1_0227664.Common
import Reasoning.WordArithmetic
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_047
import Benchmarks.Safe.V1_0227664.Blocks.Runtime_049

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.V1_0227664.RuntimeBlocks

namespace Benchmarks.Safe.V1_0227664

set_option maxRecDepth 100000

theorem safeDecrementTrace {I g s0 σ k C aw mem rdata} {value ret : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11276⟩ (value :: ret :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) (hnz : value ≠ ⟨0⟩)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD fork safeBytecode I g s0 ret (UInt256.sub value ⟨1⟩ :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_11276_taken (by simp; omega) hnz (by jump_dest) h
  have h₂ := safeRuntime_block_11290 (by omega) hret h₁
  simpa only [safeRuntime_block_11290_stack, lnot_zero_add] using ⟨_, _, h₂⟩

theorem safeDecrementUnderflow {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨11276⟩ (⟨0⟩ :: R) mem aw rdata σ k C)
    (hov : R.length + 5 ≤ 1024) : RDrev fork safeBytecode g s0 := by
  have h₁ := safeRuntime_block_11276_fallthrough (by omega) rfl h
  have h₂ := safeRuntime_block_11283
    (by simp only [safeRuntime_block_11276_fallthrough_stack, List.length_cons]; omega)
    (by jump_dest) h₁
  exact safeRuntime_block_10754
    (by simp only [safeRuntime_block_11283_stack, safeRuntime_block_11276_fallthrough_stack,
      List.length_cons]; omega) h₂

end Benchmarks.Safe.V1_0227664
