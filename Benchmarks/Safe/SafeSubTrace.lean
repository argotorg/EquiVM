import Benchmarks.Safe.CheckedSubtract
import Benchmarks.Safe.Blocks.Runtime_033
import Benchmarks.Safe.Blocks.Runtime_030

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open safeRuntimeBlocks

namespace Benchmarks.Safe

set_option maxRecDepth 100000 in
theorem safeSubTrace {I g s0 σ k C aw mem rdata} {a b ret : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7707⟩ (b :: a :: ret :: R) mem aw rdata σ k C)
    (hle : b.toNat ≤ a.toNat) (hov : R.length + 10 ≤ 1024)
    (hret : (D_J safeBytecode 0).contains ret = true) :
    ∃ k' C', RD safeBytecode I g s0 ret (UInt256.sub a b :: R) mem aw rdata σ k' C' := by
  have h₁ := safeRuntime_block_7707_taken (by simp; omega)
    (by rw [ugt_zero hle]; decide) (by jump_dest) h
  have h₂ := safeRuntime_block_7720 (by simp; omega) (by jump_dest) h₁
  obtain ⟨_, _, h₃⟩ := safeSubtractTrace h₂ (by simp; omega) hle (by jump_dest)
  exact ⟨_, _, safeRuntime_block_6891 (by omega) hret h₃⟩

theorem safeSubUnderflow {I g s0 σ k C aw mem rdata} {a b : UInt256} {R : List UInt256}
    (h : RD safeBytecode I g s0 ⟨7707⟩ (b :: a :: R) mem aw rdata σ k C)
    (hlt : a.toNat < b.toNat) (hov : R.length + 5 ≤ 1024) :
    RDrev safeBytecode g s0 := by
  have h₁ := safeRuntime_block_7707_fallthrough (by omega)
    (by rw [ugt_one hlt]; decide) h
  exact safeRuntime_block_7717 (by simp [safeRuntime_block_7707_fallthrough_stack]; omega) h₁

end Benchmarks.Safe
