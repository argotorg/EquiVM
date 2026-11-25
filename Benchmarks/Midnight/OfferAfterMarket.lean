import Benchmarks.Midnight.OfferDecodedMemory

variable {fork : Ethereum.Fork}

/-! Decode the offer fields after its nested market, through the ratifier-data offset. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightOfferAfterMarket {credit : Nat} {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw marketPtr arrayPtr callbackPtr rel : UInt256}
    {market : MarketData} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 16 ≤ 1024) (hrel : rel.toNat < 2^64)
    (hsize : I.calldata.size < UInt256.size) (hhead : rel.toNat + 4 + 480 ≤ I.calldata.size)
    (hoff : (calldataWord I.calldata (rel.toNat + 4)).toNat < 2^64)
    (hdecode : decodeMarketData I.calldata
      (rel.toNat + 4 + (calldataWord I.calldata (rel.toNat + 4)).toNat) = some market)
    (hmarket : MarketStored mem marketPtr arrayPtr callbackPtr market)
    (hlo : 1312 ≤ marketPtr.toNat)
    (hroot : memLoad (UInt256.ofNat 384) mem = ⟨832⟩)
    (hfree : memLoad (UInt256.ofNat 64) mem = callbackPtr)
    (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨10530⟩ (marketPtr :: rel :: R) mem aw rdata σ k C) :
    ((∀ offer, decodeOfferData I.calldata (rel.toNat + 4) = some offer →
        ¬ callbackPtr.toNat + returnDataAllocation offer.callbackData.size < 2^64 ∨
          decodeCalldataBytes I.calldata 36 = none) ∧ RDrev fork midnightBytecode g s0) ∨
    (∃ data,
      decodeOfferData I.calldata (rel.toNat + 4) =
        some (OfferData.at I.calldata (rel.toNat + 4) market data) ∧
      callbackPtr.toNat + returnDataAllocation data.size < 2^64 ∧
      (calldataWord I.calldata 36).toNat < 2^64 ∧
      ∃ aw' k' C',
        MemoryFunding (credit + 3 * ((data.size + 31) / 32))
          (offerDecodedMemory mem I.calldata (rel.toNat + 4) marketPtr callbackPtr) aw' C' ∧
        RD fork midnightBytecode I g s0 ⟨10833⟩ (calldataWord I.calldata 36 :: R)
          (offerDecodedMemory mem I.calldata (rel.toNat + 4) marketPtr callbackPtr)
          aw' rdata σ k' C') := by
  have hm : 416 ≤ mem.size := by
    have hs := hmarket.words.size
    change marketPtr.toNat + 32 * 8 ≤ mem.size at hs
    omega
  have hcb : 1600 ≤ callbackPtr.toNat := by
    have ha := hmarket.array
    have he := hmarket.extent
    omega
  rcases midnightOfferFirstFields (by omega) hrel hm hroot ha rd with
    ⟨hnone, hr⟩ | ⟨hb, hmaker, hcallback, hcbOff, aw1, k1, C1, ha1, rd1⟩
  · refine Or.inl ⟨?_, hr⟩
    intro offer hd
    rw [hnone] at hd
    cases hd
  · let m1 := offerFirstMemory mem I.calldata (rel.toNat + 4) marketPtr
    have hm1 : 416 ≤ m1.size := hm.trans (writeWordArray_size_ge _ _ _)
    have hr1 : memLoad (UInt256.ofNat 384) m1 = ⟨832⟩ := by
      dsimp only [m1, offerFirstMemory]
      rw [memLoad_writeWordArray_below mem 832 (UInt256.ofNat 384) _ hm (by decide), hroot]
    have hf1 : memLoad (UInt256.ofNat 64) m1 = callbackPtr := by
      dsimp only [m1, offerFirstMemory]
      rw [memLoad_writeWordArray_below mem 832 (UInt256.ofNat 64) _
        (by change 96 ≤ mem.size; omega) (by decide), hfree]
    have rd2 := midnightBlocks.midnight_block_10669 (by omega) (by jump_dest) rd1
    have ha2 := memoryFundingAt (credit := credit) rd2 (by memory_fund ha1)
    simp only [midnightBlocks.midnight_block_10669_stack] at rd2
    have hh : (rel + calldataWord I.calldata (rel.toNat + 260) + UInt256.ofNat 4).toNat =
        rel.toNat + 4 + (calldataWord I.calldata (rel.toNat + 4 + 256)).toNat := by
      have hs : (rel + calldataWord I.calldata (rel.toNat + 260)).toNat =
          rel.toNat + (calldataWord I.calldata (rel.toNat + 260)).toNat := by
        rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
      rw [uadd_word_ofNat_toNat _ 4 (by rw [hs]; change _ < 2^256; omega), hs]
      simp only [Nat.add_assoc, Nat.reduceAdd]
      omega
    have hcbOff' : (calldataWord I.calldata (rel.toNat + 4 + 256)).toNat < 2^64 := by
      simpa only [Nat.add_assoc, Nat.reduceAdd] using hcbOff
    rcases midnightBytesCalldataDecoder_funded (by simp only [List.length_cons]; omega)
        (by rw [hh]; omega) hmarket.bound hsize hf1 (by jump_dest) ha2 rd2 with
      ⟨hbad, hr⟩ | ⟨data, hd, hfit, aw3, k3, C3, ha3, rd3⟩
    · left
      refine ⟨?_, hr⟩
      intro offer hdo
      obtain ⟨_, _, _, m, data, _, hd, he⟩ := decodeOfferData_success hdo
      have hd' : decodeBytesAt I.calldata
          (rel.toNat + 4 + (calldataWord I.calldata (rel.toNat + 4 + 256)).toNat) = some data := by
        simpa only [decodeRelativeBytes, hcbOff', if_true] using hd
      rw [hh] at hbad
      exact Or.inl (by rw [he]; exact hbad data hd')
    · rw [hh] at hd ha3 rd3
      have hp := bytesCalldataMemory_prefix (mem := m1) (ptr := callbackPtr) hd
      have hr3 : memLoad (UInt256.ofNat 384)
          (offerCallbackMemory mem I.calldata (rel.toNat + 4) marketPtr callbackPtr) = ⟨832⟩ := by
        exact (hp.load (UInt256.ofNat 384) (by decide)
          (by change 384 + 32 ≤ _; omega) hm1).trans hr1
      have hm3 : 416 ≤
          (offerCallbackMemory mem I.calldata (rel.toNat + 4) marketPtr callbackPtr).size :=
        hm1.trans hp.size
      rcases midnightOfferTailFields (by simp only [List.length_cons]; omega)
          hrel hm3 hr3 ha3 rd3 with
        ⟨hnone, hr⟩ | ⟨htail, aw4, k4, C4, ha4, rd4⟩
      · refine Or.inl ⟨?_, hr⟩
        intro offer hdo
        rw [hnone] at hdo
        cases hdo
      · have hcanon : OfferData.canonicalAt I.calldata (rel.toNat + 4) := by
          refine ⟨?_, ?_, ?_, htail⟩
          · simpa only [Nat.add_assoc, Nat.reduceAdd] using hb
          · simpa only [Nat.add_assoc, Nat.reduceAdd] using hmaker
          · simpa only [Nat.add_assoc, Nat.reduceAdd] using hcallback
        have hdRel : decodeRelativeBytes I.calldata (rel.toNat + 4) 256 = some data := by
          simpa only [decodeRelativeBytes, hcbOff', if_true] using hd
        have hmax : ¬ solcMaxU64 < (calldataWord I.calldata (rel.toNat + 4)).toNat := by
          change ¬ (2^64 - 1 < _)
          omega
        have hdecoded : decodeOfferData I.calldata (rel.toNat + 4) =
            some (OfferData.at I.calldata (rel.toNat + 4) market data) := by
          simp only [decodeOfferData, hhead, hcanon, and_self, not_true_eq_false, if_false,
            hmax, hdecode, hdRel, bind, Option.bind]
          rfl
        let m4 := offerTailPrefixMemory
          (offerCallbackMemory mem I.calldata (rel.toNat + 4) marketPtr callbackPtr)
          I.calldata (rel.toNat + 4) callbackPtr
        have hr4 : memLoad (UInt256.ofNat 384) m4 = ⟨832⟩ := by
          dsimp only [m4, offerTailPrefixMemory]
          rw [memLoad_writeWordArray_below _ 1088 (UInt256.ofNat 384) _ hm3 (by decide), hr3]
        have hm4 : 416 ≤ m4.size := hm3.trans (writeWordArray_size_ge _ _ _)
        rcases midnightOfferLastFields (by omega) hrel hm4 hr4 ha4 rd4 with
          ⟨hnone, hr⟩ | ⟨hroff, aw5, k5, C5, ha5, rd5⟩
        · exact Or.inl ⟨fun _ _ ↦ Or.inr hnone, hr⟩
        · exact Or.inr ⟨data, hdecoded, hfit, hroff, aw5, k5, C5, ha5, rd5⟩

end Benchmarks.Midnight
