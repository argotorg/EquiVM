import Benchmarks.Midnight.MarketEncoder
import Benchmarks.Midnight.MemoryFunding

/-! Quantitative memory accounting for the market encoder's individual blocks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

set_option maxHeartbeats 2000000 in
theorem midnightMarketEncodeStart_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr output : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 7 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hn : memLoad arrayPtr mem = UInt256.ofNat m.collaterals.length)
    (hnin : arrayPtr.toNat + 32 ≤ mem.size)
    (hbelow : ptr.toNat + 256 ≤ output.toNat) (harray : arrayPtr.toNat + 32 ≤ output.toNat)
    (hout : output.toNat + 288 < UInt256.size) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19181⟩ (ptr :: output :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (marketEncodeHeadMemory mem output.toNat m) aw' C' ∧
      RD midnightBytecode I g s0 ⟨19261⟩
        (UInt256.ofNat 0 :: UInt256.ofNat m.collaterals.length :: (arrayPtr + UInt256.ofNat 32) ::
          ptr :: output :: (output + UInt256.ofNat 288) :: R)
        (marketEncodeHeadMemory mem output.toNat m) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19181 hstack rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_19181_memory
    memory_fund ha)
  have hr := And.intro ha1 rd1
  simp only [marketEncodeHeadBlock_memory, marketEncodeHeadBlock_stack,
    marketEncodeHeadRaw_eq m hm hn hnin hbelow harray hout] at hr
  exact ⟨_, _, _, hr⟩

theorem midnightCollateralEncodeStep_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr writePtr output index count market outputBase : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (c : CollateralData)
    (hstack : R.length + 15 ≤ 1024)
    (hptr : memLoad writePtr mem = ptr) (hm : MemoryWords mem ptr.toNat c.words)
    (hbelow : ptr.toNat + 128 ≤ output.toNat) (hout : output.toNat + 128 < UInt256.size)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19324⟩
      (index :: count :: writePtr :: market :: outputBase :: output :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding (credit + 128) (writeWordArray mem output.toNat c.words) aw' C' ∧
      RD midnightBytecode I g s0 ⟨19261⟩
        ((index + UInt256.ofNat 1) :: count :: (writePtr + UInt256.ofNat 32) ::
          market :: outputBase :: (output + UInt256.ofNat 128) :: R)
        (writeWordArray mem output.toNat c.words) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19324 hstack (by jump_dest) rd
  have ha1 := memoryFundingAt (credit := credit + 128) rd1 (by
    unfold midnightBlocks.midnight_block_19324_memory
    memory_fund ha)
  have hr := And.intro ha1 rd1
  simp only [midnightBlocks.midnight_block_19324_stack, collateralEncodeBlock_shape, hptr,
    collateralEncodeRaw_eq c hm hbelow hout] at hr
  exact ⟨_, _, _, hr⟩

theorem midnightMarketEncodeEnd_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr output finish index count readPtr ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 10 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (m.words arrayPtr))
    (hbelow : ptr.toNat + 256 ≤ output.toNat) (hout : output.toNat + 256 < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true) (ha : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨19269⟩
      (index :: count :: readPtr :: ptr :: output :: finish :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (writeWordArray mem (output.toNat + 128) m.tailWords) aw' C' ∧
      RD midnightBytecode I g s0 ret (finish :: R)
        (writeWordArray mem (output.toNat + 128) m.tailWords) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_19269 hstack hret rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_19269_memory
    memory_fund ha)
  have hr := And.intro ha1 rd1
  simp only [midnightBlocks.midnight_block_19269_stack, marketEncodeTailBlock_shape,
    marketEncodeTailRaw_eq m hm hbelow hout] at hr
  exact ⟨_, _, _, hr⟩

end Benchmarks.Midnight
