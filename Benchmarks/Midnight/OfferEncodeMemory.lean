import Benchmarks.Midnight.OfferEncoding

/-! The exact word and byte regions produced by the complete offer encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem MemoryWords.marketEncode {mem : ByteArray} {base output : Nat} {words : List UInt256}
    (h : MemoryWords mem base words) (m : MarketData) (hbelow : base + 32 * words.length ≤ output) :
    MemoryWords (marketEncodeMemory mem output m) base words :=
  ((marketEncodeHeadMemory_preserve m h hbelow).writeWords
    (m.collaterals.flatMap CollateralData.words) (Or.inl (by omega))).writeWords m.tailWords
    (Or.inl (by omega))

-- LIBRARY CANDIDATE: view a materialized byte-string header as a one-word sequence.
theorem MemoryByteString.headerWords {mem bytes : ByteArray} {ptr : UInt256}
    (h : MemoryByteString mem ptr bytes) :
    MemoryWords mem ptr.toNat [UInt256.ofNat bytes.size] := by
  refine ⟨?_, ?_, ?_⟩
  · have hb := h.bound
    change ptr.toNat + 32 * 1 < UInt256.size
    omega
  · have hs := h.size
    change ptr.toNat + 32 * 1 ≤ mem.size
    omega
  · intro ⟨i, hi⟩
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    simpa only [Nat.mul_zero, Nat.add_zero, u256_ofNat_toNat] using h.header

def offerEncodedPrefixWords (offer : OfferData) : List UInt256 :=
  offer.words (UInt256.ofNat 480) (UInt256.ofNat (offerCallbackOffset offer)) ++
    (offer.market.words (UInt256.ofNat 256) ++
      UInt256.ofNat offer.market.collaterals.length ::
        offer.market.collaterals.flatMap CollateralData.words) ++
    [UInt256.ofNat offer.callbackData.size]

theorem offerEncodedPrefixWords_length (offer : OfferData) :
    (offerEncodedPrefixWords offer).length = 25 + 4 * offer.market.collaterals.length := by
  simp only [offerEncodedPrefixWords, List.length_append, List.length_cons, List.length_nil,
    collateralWords_length,
    show (offer.words (UInt256.ofNat 480) (UInt256.ofNat (offerCallbackOffset offer))).length = 15
      from rfl,
    show (offer.market.words (UInt256.ofNat 256)).length = 8 from rfl]
  omega

set_option maxHeartbeats 800000 in
theorem offerEncodeMemory_spec {mem : ByteArray} {callbackPtr output : UInt256} (offer : OfferData)
    (hc : MemoryByteString mem callbackPtr offer.callbackData)
    (hpad : paddedSize offer.callbackData.size < 2^64)
    (hbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ output.toNat)
    (hout : output.toNat + offerEncodedSize offer + 64 < UInt256.size) :
    MemoryWords (offerEncodeMemory mem callbackPtr output offer) output.toNat
        (offerEncodedPrefixWords offer) ∧
      MemoryByteString (offerEncodeMemory mem callbackPtr output offer)
        (output + UInt256.ofNat (offerCallbackOffset offer)) offer.callbackData ∧
      MemoryPrefix mem (offerEncodeMemory mem callbackPtr output offer) output.toNat ∧
      memLoad (UInt256.ofNat 64) (offerEncodeMemory mem callbackPtr output offer) =
        memLoad (UInt256.ofNat 64) mem := by
  have hlo : 96 ≤ output.toNat := by have hl := hc.lower; omega
  have hmem : 96 ≤ mem.size := by have hl := hc.lower; have hs := hc.size; omega
  have hpadded := nat_le_paddedSize offer.callbackData.size
  have hout' : output.toNat + 864 + 128 * offer.market.collaterals.length +
      paddedSize offer.callbackData.size < UInt256.size := by
    unfold offerEncodedSize offerCallbackOffset at hout
    omega
  have hdest : (output + UInt256.ofNat (offerCallbackOffset offer)).toNat =
      output.toNat + offerCallbackOffset offer :=
    uadd_word_ofNat_toNat _ _ (by unfold offerCallbackOffset; omega)
  have hfirst : offer.encodeFirstWords.length = 6 := rfl
  have hlast : offer.encodeLastWords.length = 6 := rfl
  have hheadlen (market callback : UInt256) : (offer.words market callback).length = 15 := rfl
  have hmarketlen : (offer.market.words (UInt256.ofNat 256) ++
      UInt256.ofNat offer.market.collaterals.length ::
        offer.market.collaterals.flatMap CollateralData.words).length =
      9 + 4 * offer.market.collaterals.length := by
    simp only [List.length_append, List.length_cons, collateralWords_length,
      show (offer.market.words (UInt256.ofNat 256)).length = 8 from rfl]
    omega
  let head := writeWord mem output.toNat (UInt256.ofNat 480)
  let market := marketEncodeMemory head (output.toNat + 480) offer.market
  let first := writeWordArray market (output.toNat + 32) offer.encodeFirstWords
  let callback := offerEncodeCallbackMemory first output
    (UInt256.ofNat (offerCallbackOffset offer)) offer
  let bytes := memoryBytesEncodeMemory callback callbackPtr.toNat
    (output.toNat + offerCallbackOffset offer) offer.callbackData.size
  let result := writeWordArray bytes (output.toNat + 288) offer.encodeLastWords
  have hp0 : MemoryPrefix mem head output.toNat :=
    memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl)
  have hp1 : MemoryPrefix head market output.toNat :=
    marketEncodeMemory_prefix _ _ _ _ (by omega)
  have hp2 : MemoryPrefix market first output.toNat :=
    memoryPrefix_writeWordArray _ _ _ _ (by omega)
  have hp3 : MemoryPrefix first callback output.toNat :=
    memoryPrefix_writeWordArray _ _ _ _ (by omega)
  have hc3 : MemoryByteString callback callbackPtr offer.callbackData :=
    hc.preserve (hp0.trans (hp1.trans (hp2.trans hp3))) hbelow
  have hsrc : callbackPtr.toNat + 32 + offer.callbackData.size ≤ callback.size := by
    have hs := hc3.size
    omega
  have hp4 : MemoryPrefix callback bytes output.toNat :=
    memoryBytesEncodeMemory_prefix _ _ _ _ _ hsrc (by unfold offerCallbackOffset; omega)
  have hp5 : MemoryPrefix bytes result output.toNat :=
    memoryPrefix_writeWordArray _ _ _ _ (by omega)
  have hc4 : MemoryByteString bytes
      (output + UInt256.ofNat (offerCallbackOffset offer)) offer.callbackData := by
    have hh := memoryBytesEncodeMemory_stored hc3
      (output := output + UInt256.ofNat (offerCallbackOffset offer))
      (by rw [hdest]; unfold offerCallbackOffset; omega)
      (by rw [hdest]; unfold offerCallbackOffset; omega)
      (by rw [hdest]; unfold offerCallbackOffset; omega)
    simpa only [hdest] using hh
  have hc5 : MemoryByteString result
      (output + UInt256.ofNat (offerCallbackOffset offer)) offer.callbackData :=
    hc4.writeWords_below offer.encodeLastWords
      (by rw [hlast, hdest]; unfold offerCallbackOffset; omega) hpad
  have hh0 : MemoryWords head output.toNat [UInt256.ofNat 480] :=
    MemoryWords.of_writeWord _ _ _ (by omega)
  have hh1 : MemoryWords market output.toNat [UInt256.ofNat 480] :=
    hh0.marketEncode offer.market (by change output.toNat + 32 * 1 ≤ _; omega)
  have hh2 : MemoryWords first output.toNat ([UInt256.ofNat 480] ++ offer.encodeFirstWords) := by
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.mul_one] using
      hh1.append_writeWordArray offer.encodeFirstWords (by
        simp only [List.length_append, List.length_cons, List.length_nil, hfirst]; omega)
  have hh3 : MemoryWords callback output.toNat
      (([UInt256.ofNat 480] ++ offer.encodeFirstWords) ++
        [UInt256.ofNat offer.callback.val, UInt256.ofNat (offerCallbackOffset offer)]) := by
    simpa only [List.length_append, List.length_cons, List.length_nil, hfirst, Nat.reduceAdd,
      Nat.reduceMul, offerEncodeCallbackMemory] using
      hh2.append_writeWordArray [UInt256.ofNat offer.callback.val,
        UInt256.ofNat (offerCallbackOffset offer)] (by
          simp only [List.length_append, List.length_cons, List.length_nil, hfirst]; omega)
  have hh4 := hh3.memoryBytesEncode (ptr := callbackPtr.toNat)
    (output := output.toNat + offerCallbackOffset offer) hsrc (by
    simp only [List.length_append, List.length_cons, List.length_nil, hfirst]
    unfold offerCallbackOffset
    omega)
  have hh5 : MemoryWords result output.toNat
      (offer.words (UInt256.ofNat 480) (UInt256.ofNat (offerCallbackOffset offer))) := by
    have hh := hh4.append_writeWordArray offer.encodeLastWords (by
      simp only [List.length_append, List.length_cons, List.length_nil, hfirst, hlast]; omega)
    simpa only [List.length_append, List.length_cons, List.length_nil, hfirst, Nat.reduceAdd,
      Nat.reduceMul, OfferData.encodeFirstWords, OfferData.encodeLastWords,
      OfferData.encodeLastFour, OfferData.words, List.cons_append, List.nil_append] using hh
  have hm1 := marketEncodeMemory_words head (output.toNat + 480) offer.market (by omega)
  have hm2 := hm1.writeWords offer.encodeFirstWords (off := output.toNat + 32)
    (Or.inr (by rw [hfirst]; omega))
  have hm3 := hm2.writeWords [UInt256.ofNat offer.callback.val,
    UInt256.ofNat (offerCallbackOffset offer)] (off := output.toNat + 224)
    (Or.inr (by simp only [List.length_cons, List.length_nil]; omega))
  have hm4 := hm3.memoryBytesEncode (ptr := callbackPtr.toNat)
    (output := output.toNat + offerCallbackOffset offer) hsrc (by
      rw [hmarketlen]; unfold offerCallbackOffset; omega)
  have hm5 : MemoryWords result (output.toNat + 480)
      (offer.market.words (UInt256.ofNat 256) ++
        UInt256.ofNat offer.market.collaterals.length ::
          offer.market.collaterals.flatMap CollateralData.words) :=
    hm4.writeWords offer.encodeLastWords (Or.inr (by rw [hlast]))
  have hhmarket := hh5.append (by
    change MemoryWords result (output.toNat + 32 * 15) _
    exact hm5)
  have hall : MemoryWords result output.toNat (offerEncodedPrefixWords offer) :=
    hhmarket.append (by
      have hh := hc5.headerWords
      rw [hdest] at hh
      convert hh using 1
      simp only [List.length_append, hmarketlen, hheadlen, offerCallbackOffset]
      omega)
  have hf0 : MemoryWords mem 64 [memLoad (UInt256.ofNat 64) mem] := by
    refine ⟨by change 96 < UInt256.size; decide, hmem, ?_⟩
    intro ⟨i, hi⟩
    have he : i = 0 := by change i < 1 at hi; omega
    subst i
    rfl
  have hf1 := (hf0.writeWord (UInt256.ofNat 480) (off := output.toNat)
    (Or.inl (by change 96 ≤ output.toNat; exact hlo))).marketEncode offer.market (by
      change 96 ≤ output.toNat + 480; omega)
  have hf2 := hf1.writeWords offer.encodeFirstWords (off := output.toNat + 32)
    (Or.inl (by change 96 ≤ _; omega))
  have hf3 := hf2.writeWords [UInt256.ofNat offer.callback.val,
    UInt256.ofNat (offerCallbackOffset offer)] (off := output.toNat + 224)
    (Or.inl (by change 96 ≤ _; omega))
  have hf4 := hf3.memoryBytesEncode (ptr := callbackPtr.toNat)
    (output := output.toNat + offerCallbackOffset offer) hsrc (by
      change 96 ≤ _; unfold offerCallbackOffset; omega)
  have hf5 := hf4.writeWords offer.encodeLastWords (off := output.toNat + 288)
    (Or.inl (by change 96 ≤ _; omega))
  exact ⟨hall, hc5, hp0.trans (hp1.trans (hp2.trans (hp3.trans (hp4.trans hp5)))),
    hf5.load_word ⟨0, by change 0 < 1; decide⟩ rfl⟩

end Benchmarks.Midnight
