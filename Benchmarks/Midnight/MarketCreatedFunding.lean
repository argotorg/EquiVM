import Benchmarks.Midnight.MarketCreatedTrace
import Benchmarks.Midnight.MarketEncoderFunding

/-! Paid memory growth through the MarketCreated event. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES midnightMarketCreated with retained funding.
set_option maxRecDepth 2000000 in
theorem midnightMarketCreated_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw ptr arrayPtr limit root id ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (m : MarketData)
    (hstack : R.length + 22 ≤ 1024) (hm : MarketStored mem ptr arrayPtr limit m)
    (hlimit : limit.toNat ≤ root.toNat) (hb : root.toNat + m.encodingSize < UInt256.size)
    (hfree : memLoad (UInt256.ofNat 64) mem = root) (hperm : I.perm = true)
    (hret : (D_J midnightBytecode 0).contains ret = true)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨21682⟩ (ptr :: id :: ret :: R)
      mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit (marketCreatedMemory mem root m) aw' C' ∧ RD midnightBytecode I g s0 ret (id :: R)
      (marketCreatedMemory mem root m) aw' rdata σ k' C' := by
  have rd1 := midnightBlocks.midnight_block_21682
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  have hfund1 := memoryFundingAt (credit := credit) rd1 (by
    unfold midnightBlocks.midnight_block_21682_memory
    memory_fund hfund)
  simp only [midnightBlocks.midnight_block_21682_stack,
    midnightBlocks.midnight_block_21682_memory, hfree] at rd1 hfund1
  let mem1 := writeWord mem root.toNat (UInt256.ofNat 32)
  change RD _ _ _ _ _ _ mem1 _ _ _ _ _ at rd1
  change MemoryFunding credit mem1 _ _ at hfund1
  have hp : MemoryPrefix mem mem1 limit.toNat :=
    memoryPrefix_writeWord _ _ _ _ (Or.inl hlimit)
  have hm1 := hm.preserve hp
  have ho : (root + UInt256.ofNat 32).toNat = root.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by dsimp only [MarketData.encodingSize] at hb; omega)
  obtain ⟨aw2, k2, C2, hfund2, rd2⟩ := midnightMarketEncoder_funded m
    (by simp only [List.length_cons]; omega) hm1.words
    (hm1.header.load_word ⟨0, by simp⟩ (by simp)) (by simpa using hm1.header.size)
    hm1.collaterals (by have := hm.array; have := hm.extent; omega) hm.extent
    (by rw [ho]; omega) (by rw [ho]; dsimp only [MarketData.encodingSize] at hb; omega)
    (by jump_dest) hfund1 rd1
  have rd3 := midnightBlocks.midnight_block_21739
    (by omega) hperm hret rd2
  have hfund3 := memoryFundingAt (credit := credit) rd3 (by memory_fund hfund2)
  simp only [midnightBlocks.midnight_block_21739_stack, ho] at rd3 hfund3
  exact ⟨_, _, _, hfund3, rd3⟩


end Benchmarks.Midnight
