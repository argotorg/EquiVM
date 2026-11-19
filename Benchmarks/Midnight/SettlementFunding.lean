import Benchmarks.Midnight.SettlementReadFunding
import Benchmarks.Midnight.SettlementComputeGas

/-! The settlement-fee routine retains the caller's memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES settlementInternalTrace with a retained funding invariant.
theorem settlementInternalTrace_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw id time ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 17 ≤ 1024) (hmem : 64 ≤ mem.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hspace : marketTickSpacing (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) ≠ ⟨0⟩)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨21835⟩ (id :: time :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (twoWordHashMem id ⟨1⟩ mem) aw' C' ∧
      RD midnightBytecode I g s0 ret
        (settlementFeeValue (solcSlotWordAt (solcMappingSlot ⟨1⟩ id + ⟨2⟩) σ I) time :: R)
        (twoWordHashMem id ⟨1⟩ mem) aw' rdata σ k' C' := by
  obtain ⟨aw1, k1, C1, ha1, rd1⟩ := settlementRead_funded
    (by simp only [List.length_cons]; omega) hmem hspace ha rd
  obtain ⟨k2, C2, hC2, rd2⟩ := settlementComputeTrace_mono hstack hret rd1
  exact ⟨aw1, k2, C2, ha1.mono hC2, rd2⟩

end Benchmarks.Midnight
