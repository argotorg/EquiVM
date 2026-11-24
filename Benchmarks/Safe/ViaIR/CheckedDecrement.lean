import Benchmarks.Safe.ViaIR.Common
import Reasoning.WordArithmetic
import Benchmarks.Safe.ViaIR.Blocks.Runtime_005
import Benchmarks.Safe.ViaIR.Blocks.Runtime_006

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Safe.ViaIR.RuntimeBlocks

namespace Benchmarks.Safe.ViaIR

set_option maxRecDepth 100000

-- The IR pipeline checks underflow before the block that decrements and stores the count.
theorem safeDecrementTrace {I g s0 σ k C aw mem rdata} {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨639⟩ R mem aw rdata σ k C)
    (hov : R.length + 3 ≤ 1024) (hnz : solcSlotWordAt ⟨3⟩ σ I ≠ ⟨0⟩) :
    ∃ k' C', RD fork safeBytecode I g s0 ⟨649⟩ (solcSlotWordAt ⟨3⟩ σ I :: R)
      mem aw rdata σ k' C' := by
  exact safeRuntime_block_639_fallthrough hov (isZero_eq_zero_of_ne hnz) h

theorem safeDecrementUnderflow {I g s0 σ k C aw mem rdata} {key prev threshold : UInt256}
    {R : List UInt256}
    (h : RD fork safeBytecode I g s0 ⟨639⟩ (key :: prev :: threshold :: ⟨0⟩ :: R)
      mem aw rdata σ k C)
    (hov : R.length + 7 ≤ 1024) (hz : solcSlotWordAt ⟨3⟩ σ I = ⟨0⟩) :
    RDrev fork safeBytecode g s0 := by
  obtain ⟨_, _, h879⟩ := safeRuntime_block_639_taken (by simp; omega)
    (by change UInt256.isZero (solcSlotWordAt ⟨3⟩ σ I) ≠ ⟨0⟩; rw [hz]; decide)
    (by jump_dest) h
  exact safeRuntime_block_879 hov h879

end Benchmarks.Safe.ViaIR
