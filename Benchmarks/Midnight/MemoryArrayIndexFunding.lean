import Benchmarks.Midnight.ArrayIndexGas
import Benchmarks.Midnight.FundingBudget

/-! Memory funding through the array-index helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES midnightMemoryArrayIndex with retained memory funding.
set_option maxRecDepth 2000000 in
theorem midnightMemoryArrayIndex_memoryFunded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr index ret : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 5 ≤ 1024)
    (hi : index.toNat < 2^64) (hlt : index.toNat < (memLoad ptr mem).toNat)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19460⟩ (ptr :: index :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit mem aw' C' ∧ RD midnightBytecode I g s0 ret
      (((ptr + UInt256.ofNat 32) + UInt256.ofNat (32 * index.toNat)) :: R)
      mem aw' rdata σ k' C' := by
  obtain ⟨aw', k', C', hb, rd'⟩ :=
    midnightMemoryArrayIndex_funded hstack hi hlt hret hfund.budget rd
  exact ⟨aw', k', C', hb.funding, rd'⟩

end Benchmarks.Midnight
