import Reasoning.Reach
import Tests.Pipeline.VyperRegistry.Bytecode

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM
open Reasoning.Theory Reasoning.Reach

namespace registryBlocks

/-- Final stack for bytecode block summary `registry_block_1681`. -/
def registry_block_1681_stack {x0 : UInt256} {x1 : UInt256} {R : List UInt256} : List UInt256 :=
  ((UInt256.sdiv x0 x1) :: R)

/-- Automatically generated RD summary for bytecode block at pc 1681. -/
theorem registry_block_1681 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1681) (x0 :: x1 :: R) mem aw rdata σ k C)
    : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1682) (registry_block_1681_stack (x0 := x0) (x1 := x1) (R := R)) mem aw rdata σ (k + 1) (C + ((5))) := by
  let r0 := h
  have r1 := r0.sdiv (by native_decide) (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 1682)) r1 (by native_decide)
  exact RD.normalizeCounters rFinal (by omega) (by omega)

/-- Packed RD summary for bytecode block with abstract final counters and active words. -/
theorem registry_block_1681_packed {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 : UInt256} {R : List UInt256}
    (hstack : R.length + 2 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1681) (x0 :: x1 :: R) mem aw rdata σ k C)
    : ∃ (aw' : UInt256) (k' C' : ℕ), RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1682) (registry_block_1681_stack (x0 := x0) (x1 := x1) (R := R)) mem aw' rdata σ k' C' := by
  obtain ⟨k', C', h'⟩ := RD.pack (registry_block_1681 hstack h)
  exact ⟨_, k', C', h'⟩

/- Unsupported instruction boundary at pc 1682: unsupported_ce (0xce). No RD transition is asserted. Summaries resume at pc 1683 from a fresh symbolic RD state. -/

/-- Automatically generated RD summary for bytecode block at pc 1683. -/
theorem registry_block_1683 {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 3 ≤ 1024)
    (h : RD fork Tests.Pipeline.VyperRegistry.registryBytecode ee g s0 (UInt256.ofNat 1683) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : RDrev fork Tests.Pipeline.VyperRegistry.registryBytecode g s0 := by
  let r0 := h
  have r1 := r0.sdiv (by native_decide) (by evm_ov)
  exact RD.genRev r1 (by native_decide) (by evm_ov)

end registryBlocks
