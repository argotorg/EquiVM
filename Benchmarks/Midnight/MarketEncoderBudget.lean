import Benchmarks.Midnight.MarketEncoderFunding
import Benchmarks.Midnight.MarketEncoder
import Benchmarks.Midnight.TransferBudget

variable {fork : Ethereum.Fork}

/-! Market encoding with either a small transfer heap or retained memory funding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem midnightMarketEncoder_budget {budgetRoot : UInt256} {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr output ret : UInt256}
    {σ : AccountMap} {limit k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 16 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hn : memLoad arrayPtr mem = UInt256.ofNat m.collaterals.length)
    (hnin : arrayPtr.toNat + 32 ≤ mem.size)
    (hc : CollateralListStored mem (arrayPtr + UInt256.ofNat 32) limit m.collaterals)
    (hbelow : ptr.toNat + 256 ≤ limit) (harray : arrayPtr.toNat + 32 ≤ limit)
    (hlimit : limit ≤ output.toNat)
    (hout : output.toNat + 288 + 128 * m.collaterals.length < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (ha : TransferBudget budgetRoot credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨19181⟩ (ptr :: output :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', TransferBudget budgetRoot (credit + 128 * m.collaterals.length) (marketEncodeMemory mem output.toNat m) aw' C' ∧
      RD fork midnightBytecode I g s0 ret
      ((output + UInt256.ofNat (288 + 128 * m.collaterals.length)) :: R)
      (marketEncodeMemory mem output.toNat m) aw' rdata σ k' C' := by
  rcases ha with hsmall | ⟨halign, hfund⟩
  · obtain ⟨aw', k', C', rd'⟩ := midnightMarketEncoder m hstack hm hn hnin hc hbelow
      harray hlimit hout hret rd
    exact ⟨aw', k', C', Or.inl hsmall, rd'⟩
  · obtain ⟨aw', k', C', hf, rd'⟩ := midnightMarketEncoder_funded m hstack hm hn hnin hc
      hbelow harray hlimit hout hret hfund rd
    exact ⟨aw', k', C', Or.inr ⟨halign, hf⟩, rd'⟩

end Benchmarks.Midnight
