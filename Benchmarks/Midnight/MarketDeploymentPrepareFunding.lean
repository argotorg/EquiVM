import Benchmarks.Midnight.MarketDeploymentPrepare
import Benchmarks.Midnight.Sstore2PrefixFunding
import Benchmarks.Midnight.MarketDeploymentBytesFunding
import Benchmarks.Midnight.MarketDeploymentConcatFunding

variable {fork : Ethereum.Fork}

/-! Funded construction of the exact market deployment bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- GENERALIZES midnightMarketDeploymentPrepare with retained funding.
set_option maxRecDepth 2000000 in
theorem midnightMarketDeploymentPrepare_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw root ptr arrayPtr limit : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (m : MarketData) (hstack : R.length + 22 ≤ 1024)
    (hm : MarketStored mem ptr arrayPtr limit m) (hlimit : limit.toNat ≤ root.toNat)
    (hb : root.toNat + 2 * m.encodingSize + 288 < 2^64)
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hfund : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨24347⟩ (UInt256.ofNat 21556 :: ptr :: R)
      mem aw rdata σ k C) :
    MemoryPrefix mem (marketDeploymentMemory mem root m) limit.toNat ∧
    memLoad (UInt256.ofNat 64) (marketDeploymentMemory mem root m) = marketDeploymentFree root m ∧
    (marketDeploymentMemory mem root m).readWithPadding
      (marketIdInitcodePtr root m + UInt256.ofNat 32).toNat
      (UInt256.ofNat (11 + m.encodingSize)).toNat = m.initcode ∧
    ∃ aw' k' C', MemoryFunding credit (marketDeploymentMemory mem root m) aw' C' ∧ RD fork midnightBytecode I g s0 ⟨21667⟩
      (⟨0⟩ :: (marketIdInitcodePtr root m + UInt256.ofNat 32) ::
        UInt256.ofNat (11 + m.encodingSize) :: ⟨0⟩ :: ptr :: R)
      (marketDeploymentMemory mem root m) aw' rdata σ k' C' := by
  let ep := marketIdEncodedPtr root
  let cp := marketIdInitcodePtr root m
  let mem1 := sstore2PrefixMemory mem root
  let mem2 := marketBytesMemory mem1 ep m
  let mem3 := marketInitcodeMemory mem2 cp root ep m
  have hlo : 96 ≤ root.toNat := by
    have := hm.lower; have := hm.array; have := hm.extent; omega
  rcases marketIdPointers m hb with ⟨he, hc, _⟩
  change ep.toNat = root.toNat + 64 at he
  change cp.toNat = root.toNat + m.encodingSize + 96 at hc
  obtain ⟨aw1, k1, C1, hfund1, rd1⟩ := midnightSstore2Prefix_funded
    (by simp only [List.length_cons]; omega) (by omega) hfree (by jump_dest) hfund rd
  change RD fork _ _ _ _ _ _ mem1 _ _ _ _ _ at rd1
  change MemoryFunding credit mem1 aw1 C1 at hfund1
  have hf1 : memLoad (UInt256.ofNat 64) mem1 = ep := sstore2PrefixMemory_free mem hlo
  have hp1 := sstore2PrefixMemory_prefix mem root
  have hm1 := hm.preserve (hp1.mono hlimit)
  have rd2 := midnightBlocks.midnight_block_21556 (by omega)
    (by jump_dest) rd1
  have hfund2 := memoryFundingAt (credit := credit) rd2 (by
    unfold midnightBlocks.midnight_block_21556_memory
    memory_fund hfund1)
  have he32 : (ep + UInt256.ofNat 32).toNat = ep.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by rw [he]; change _ < 2^256; omega)
  simp only [midnightBlocks.midnight_block_21556_stack,
    midnightBlocks.midnight_block_21556_memory, hf1, he32] at rd2 hfund2
  obtain ⟨aw3, k3, C3, hfund3, rd3⟩ := midnightMarketDeploymentBytes_funded m
    (by simp only [List.length_cons]; omega) hm1 (by rw [he]; omega)
    (by rw [he]; omega) hfund2 rd2
  change RD fork _ _ _ _ _ _ mem2 _ _ _ _ _ at rd3
  change MemoryFunding credit mem2 aw3 C3 at hfund3
  have hp2 := marketBytesMemory_prefix mem1 ep m
  have hs1 : root.toNat + 64 ≤ mem1.size := sstore2PrefixMemory_size mem root
  have hpLen : memLoad root mem2 = UInt256.ofNat 11 := by
    rw [hp2.load root hlo (by rw [he]; omega) (by omega), sstore2PrefixMemory_length]
  have hpBytes : mem2.readWithPadding (root.toNat + 32) 11 = Model.sstore2Prefix := by
    rw [hp2.read_window (by omega) (by rw [he]) hs1 (by decide) (by decide),
      sstore2PrefixMemory_bytes]
  have hwords := marketBytesMemory_words mem1 m (root := ep) (by rw [he]; omega)
    (by rw [he]; change _ < 2^256; omega)
  have heSize : ep.toNat + 32 + m.encodingSize ≤ mem2.size := by
    simpa only [← m.encodingSize_eq] using hwords.size
  have heBytes : mem2.readWithPadding (ep.toNat + 32) m.encodingSize =
      wordArrayBytes m.encodedWords := by rw [m.encodingSize_eq]; exact hwords.read
  have hf2 : memLoad (UInt256.ofNat 64) mem2 = cp := marketBytesMemory_free mem1 ep m
  have heLen : memLoad ep mem2 = UInt256.ofNat m.encodingSize :=
    marketBytesMemory_length mem1 m (by rw [he]; omega)
  obtain ⟨aw4, k4, C4, hfund4, rd4⟩ := midnightMarketDeploymentConcat_funded m
    (by simp only [List.length_cons]; omega) (by rw [hc]; omega)
    (by have := hp2.size; omega) (by rw [hc]; omega) (by omega)
    (by rw [hc, he]; omega) hf2 hpLen heLen hfund3 rd3
  change RD fork _ _ _ _ _ _ mem3 _ _ _ _ _ at rd4
  change MemoryFunding credit mem3 aw4 C4 at hfund4
  have hcBytes : mem3.readWithPadding (cp.toNat + 32) (11 + m.encodingSize) = m.initcode :=
    marketInitcodeMemory_bytes mem2 m (by rw [hc]; omega) (by omega)
      (by have := hp2.size; omega) heSize (by rw [hc, he]; omega) hpBytes heBytes
  have hp3 := marketInitcodeMemory_prefix mem2 cp root ep m (by have := hp2.size; omega) heSize
  have hcLen : memLoad cp mem3 = UInt256.ofNat (11 + m.encodingSize) :=
    marketInitcodeMemory_length mem2 m (by rw [hc]; omega)
  have hf3 : memLoad (UInt256.ofNat 64) mem3 = marketDeploymentFree root m :=
    marketInitcodeMemory_free mem2 cp root ep m
  have rd5 := midnightBlocks.midnight_block_21662 (by simp only [List.length_cons]; omega) rd4
  have hfund5 := memoryFundingAt (credit := credit) rd5 (by memory_fund hfund4)
  simp only [midnightBlocks.midnight_block_21662_stack, hcLen] at rd5 hfund5
  refine ⟨(hp1.mono hlimit).trans ((hp2.mono (by rw [he]; omega)).trans
    (hp3.mono (by rw [hc]; omega))), hf3, ?_, _, _, _, hfund5, rd5⟩
  change mem3.readWithPadding (cp + UInt256.ofNat 32).toNat
    (UInt256.ofNat (11 + m.encodingSize)).toNat = m.initcode
  simpa only [uadd_word_ofNat_toNat cp 32 (by rw [hc]; change _ < 2^256; omega),
    UInt256.toNat_ofNat_of_lt (show 11 + m.encodingSize < UInt256.size by change _ < 2^256; omega)]
    using hcBytes


end Benchmarks.Midnight
