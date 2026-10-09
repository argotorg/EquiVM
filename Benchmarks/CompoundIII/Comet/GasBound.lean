import Solm.Refine

open Solm Ethereum

namespace Benchmarks.CompoundIII.Comet

/-- Maximum allocation by one `absorbInternal` call, over all 8-bit asset counts. -/
def absorbAllocationPerAccount : Nat := 480 + 1856 * 255

/-- Heap budget including the initial free pointer and the largest lookahead after an account. -/
def absorbMemoryBudget (accounts : Nat) : Nat :=
  128 + accounts * absorbAllocationPerAccount + 256

/-- Gas restriction for the runtime refinement. The public accounts loop charges 214 gas before
entering `absorbInternal` and 15 gas on its back edge, excluding the internal call's own cost.
This is the largest bound justified by those charges and the per-account allocation estimate. -/
def cometGasBound : GasBound := fun g ↦
  absorbMemoryBudget ((g.toNat + 15) / 229) < 2^64

theorem cometGasBound_iff (g : UInt256) :
    cometGasBound g ↔ g.toNat < 8916549292636669 := by
  simp only [cometGasBound, absorbMemoryBudget, absorbAllocationPerAccount]
  omega

theorem cometGasBound_above_minimum : (2^24 : Nat) < 8916549292636669 := by decide

theorem absorbMemoryBudget_entry {gas i free assets : Nat}
    (hgas : absorbMemoryBudget ((gas + 15) / 229) < 2^64)
    (hspent : 229 * i + 214 ≤ gas)
    (hfree : free ≤ 128 + i * absorbAllocationPerAccount) (hassets : assets < 256) :
    free + 480 + 1856 * assets + 256 < 2^64 := by
  simp only [absorbMemoryBudget, absorbAllocationPerAccount] at *
  omega

theorem absorbMemoryBudget_exit {gas i free : Nat}
    (hgas : absorbMemoryBudget ((gas + 15) / 229) < 2^64)
    (hspent : 229 * i ≤ gas)
    (hfree : free ≤ 128 + i * absorbAllocationPerAccount) :
    free + 256 < 2^64 := by
  simp only [absorbMemoryBudget, absorbAllocationPerAccount] at *
  omega

end Benchmarks.CompoundIII.Comet
