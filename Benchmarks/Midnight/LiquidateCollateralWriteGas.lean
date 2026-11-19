import Benchmarks.Midnight.RuntimeBlocks_027
import Benchmarks.Midnight.CollateralBlocksGas

/-! The collateral read retains the cost of expanding memory for the seized amount. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight
open midnightBlocks

set_option maxRecDepth 10000

-- GENERALIZES the generated block at 6775 with a memory-payment lower bound.
theorem liquidate_block_6775_paid {ee : ExecutionEnv} {g : Sat256} {s0 : State} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : ℕ} {x0 x1 x2 : UInt256} {R : List UInt256}
    (hstack : R.length + 4 ≤ 1024)
    (hvalid : (D_J Benchmarks.Midnight.midnightBytecode 0).contains (UInt256.ofNat 23403) = true)
    (h : RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 6775) (x0 :: x1 :: x2 :: R) mem aw rdata σ k C)
    : ∃ (k' C' : ℕ), C + memExpansionCost aw (UInt256.ofNat 640) ⟨32⟩ ≤ C' ∧ RD Benchmarks.Midnight.midnightBytecode ee g s0 (UInt256.ofNat 23403) (midnight_block_6775_stack (ee := ee) (mem := mem) (σ := σ) (x0 := x0) (x1 := x1) (x2 := x2) (R := R)) mem (M aw (UInt256.ofNat 640) (⟨32⟩ : UInt256)) rdata σ k' C' := by
  let r0 := h
  have r1 := r0.jumpdest (by native_decide) (by evm_ov)
  have r2 := r1.swap1 (by native_decide) (by evm_ov)
  obtain ⟨_, _, hc, r3⟩ := RD.sloadMono r2 (by native_decide) (by evm_ov)
  have r4 := r3.swap1 (by native_decide) (by evm_ov)
  have r5 := r4.push1 (UInt256.ofNat 3) (by native_decide) (by evm_ov)
  have r6 := r5.shl (by native_decide) (by evm_ov)
  have r7 := r6.shr (by native_decide) (by evm_ov)
  have r8 := r7.and (by native_decide) (by evm_ov)
  have r9 := r8.push2 (UInt256.ofNat 6795) (by native_decide) (by evm_ov)
  have r10 := r9.push2 (UInt256.ofNat 640) (by native_decide) (by evm_ov)
  have r11 := RD.genMload r10 (by native_decide) (by evm_ov)
  have r12 := r11.push2 (UInt256.ofNat 23403) (by native_decide) (by evm_ov)
  have r13 := r12.jump (by native_decide) hvalid (by evm_ov)
  have rFinal := RD.normalizePC (pc' := (UInt256.ofNat 23403)) r13 (by native_decide)
  exact ⟨_, _, by omega, rFinal⟩

end Benchmarks.Midnight
