import Benchmarks.Midnight.OfferPrepare
import Benchmarks.Midnight.OfferAfterMarket
import Benchmarks.Midnight.MarketDecoderPreserved
import Benchmarks.Midnight.MarketCalldataHugeRuntime
import Benchmarks.Midnight.MemorySnapshot

/-! The complete offer decoder, including its nested market and callback data. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightOfferDecoder {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw : UInt256} {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 32 ≤ 1024) (hsize : I.calldata.size < UInt256.size)
    (hmem : 832 ≤ mem.size) (hfree : memLoad (UInt256.ofNat 64) mem = ⟨832⟩)
    (ha : MemoryAccounting mem aw C)
    (rd : RD midnightBytecode I g s0 ⟨10425⟩ R mem aw rdata σ k C) :
    ((∀ offer, decodeCalldataOffer I.calldata 4 = some offer →
        ¬ 1632 + 160 * offer.market.collaterals.length + paddedSize offer.callbackData.size <
          2^64 ∨ decodeCalldataBytes I.calldata 36 = none) ∧ RDrev midnightBytecode g s0) ∨
    (∃ offer, decodeCalldataOffer I.calldata 4 = some offer ∧
      I.calldata.size < 2^255 ∧ (calldataWord I.calldata 36).toNat < 2^64 ∧
      ∃ mem' callbackPtr root aw' k' C',
        callbackPtr.toNat = 1600 + 160 * offer.market.collaterals.length ∧
        root.toNat = 1632 + 160 * offer.market.collaterals.length +
          paddedSize offer.callbackData.size ∧
        OfferStored mem' ⟨832⟩ ⟨1312⟩ ⟨1568⟩ callbackPtr root offer ∧
        memLoad (UInt256.ofNat 64) mem' = root ∧ root.toNat ≤ mem'.size ∧
        MemoryWords mem' 96 (memoryWordSnapshot (offerPrepareMemory mem) 96 23) ∧
        MemoryFunding (3 * ((offer.callbackData.size + 31) / 32)) mem' aw' C' ∧
        RD midnightBytecode I g s0 ⟨10833⟩ (calldataWord I.calldata 36 :: R)
          mem' aw' rdata σ k' C') := by
  rcases midnightOfferPrepare (by omega) hfree ha rd with
    ⟨hnone, hr⟩ | ⟨ho, hh, hmoff, aw1, k1, C1, ha1, rd1⟩
  · refine Or.inl ⟨?_, hr⟩
    intro offer hd
    rw [hnone] at hd
    cases hd
  have hhead : (calldataWord I.calldata 4 +
      calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat) + UInt256.ofNat 4).toNat =
      (calldataWord I.calldata 4).toNat + 4 +
        (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
    have hs : (calldataWord I.calldata 4 +
        calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat =
        (calldataWord I.calldata 4).toNat +
          (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat)).toNat := by
      rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
    rw [uadd_word_ofNat_toNat _ 4 (by rw [hs]; change _ < 2^256; omega), hs]
    omega
  by_cases hsmall : I.calldata.size < 2^255
  · have hdecode : decodeCalldataOffer I.calldata 4 =
        decodeOfferData I.calldata ((calldataWord I.calldata 4).toNat + 4) := by
      have hcap : ¬ solcMaxU64 < (calldataWord I.calldata 4).toNat := by
        change ¬ (2^64 - 1 < _)
        omega
      simp only [decodeCalldataOffer, hcap, not_le_of_gt hsmall, or_self, if_false]
      rw [Nat.add_comm 4]
    have hfithead : (calldataWord I.calldata 4).toNat + 4 + 480 ≤ I.calldata.size := by
      have ht := calldataArgumentHead_toNat ho
      change (UInt256.ofNat 4 + calldataWord I.calldata 4).toNat = _ at ht
      have hc := signedDecodeCheck (finish := UInt256.ofNat I.calldata.size)
        (start := UInt256.ofNat 4 + calldataWord I.calldata 4) (need := 480)
        (by rw [UInt256.toNat_ofNat_of_lt hsize]; exact hsmall)
        (by rw [ht]; omega) (by decide)
      change UInt256.slt (UInt256.sub (UInt256.ofNat I.calldata.size)
        (calldataWord I.calldata 4) + UInt256.lnot ⟨3⟩) (UInt256.ofNat 480) = _ at hh
      rw [u256_add_comm, lnot3_add_sub_word, hc] at hh
      rw [UInt256.toNat_ofNat_of_lt hsize, ht] at hh
      by_contra h
      rw [decide_eq_true (by omega)] at hh
      exact (by decide : (UInt256.ofNat 1 : UInt256) ≠ UInt256.ofNat 0) hh
    have hkeep := MemoryWords.snapshot (offerPrepareMemory mem) 96 23
      (by decide) (by rw [offerPrepareMemory_size hmem]; exact hmem)
    rcases midnightMarketCalldataDecoder_preserved
        (by simp only [List.length_cons]; omega) hsmall (by rw [hhead]; omega)
        (by decide) (by decide) (offerPrepareMemory_free mem) (by jump_dest)
        hkeep (by decide) (by rw [memoryWordSnapshot_length]; decide) ha1 rd1 with
      ⟨hbad, hr⟩ | ⟨market, hmarketDec, hmarketFit, mem2, callbackPtr, aw2, k2, C2,
        hcallbackPtr, hmarket, hf2, hm2, hk2, ha2, rd2⟩
    · refine Or.inl ⟨?_, hr⟩
      intro offer hd
      rw [hdecode] at hd
      obtain ⟨_, _, _, market, data, hmd, _, he⟩ := decodeOfferData_success hd
      rw [hhead, Nat.add_comm 4] at hbad
      have hb := hbad market hmd
      change ¬ 1600 + 160 * market.collaterals.length < 2^64 at hb
      left
      rw [he]
      change ¬ 1632 + 160 * market.collaterals.length + paddedSize data.size < 2^64
      omega
    · rw [hhead, Nat.add_comm 4] at hmarketDec
      change callbackPtr.toNat = 1600 + 160 * market.collaterals.length at hcallbackPtr
      have hr2 : memLoad (UInt256.ofNat 384) mem2 = ⟨832⟩ :=
        (hk2.snapshot_load 9 (by decide)).trans (offerPrepareMemory_root mem)
      have hoff : (calldataWord I.calldata ((calldataWord I.calldata 4).toNat + 4)).toNat <
          2^64 := by simpa only [Nat.add_comm 4] using hmoff
      rcases midnightOfferAfterMarket (by omega) ho hsize hfithead hoff hmarketDec hmarket
          (by decide) hr2 hf2 (MemoryFunding.of_accounting ha2) rd2 with
        ⟨hbad, hr⟩ | ⟨data, hdo, hdataFit, hratOff, aw3, k3, C3, ha3, rd3⟩
      · refine Or.inl ⟨?_, hr⟩
        intro offer hd
        rw [hdecode] at hd
        rcases hbad offer hd with hb | hb
        · left
          obtain ⟨_, _, _, m, d, hmd, _, he⟩ := decodeOfferData_success hd
          have heq : m = market := Option.some.inj (hmd.symm.trans hmarketDec)
          rw [he, heq] at hb ⊢
          change ¬ callbackPtr.toNat + returnDataAllocation d.size < 2^64 at hb
          rw [hcallbackPtr, returnDataAllocation_eq] at hb
          change ¬ 1632 + 160 * market.collaterals.length + paddedSize d.size < 2^64
          omega
        · exact Or.inr hb
      · obtain ⟨_, hcanon, _, m, d, _, hrelData, he⟩ := decodeOfferData_success hdo
        have hedata : data = d := congrArg OfferData.callbackData he
        rw [← hedata] at hrelData
        have hd : decodeBytesAt I.calldata ((calldataWord I.calldata 4).toNat + 4 +
            (calldataWord I.calldata ((calldataWord I.calldata 4).toNat + 4 + 256)).toNat) =
            some data := by
          unfold decodeRelativeBytes at hrelData
          dsimp only at hrelData
          split at hrelData
          · exact hrelData
          · cases hrelData
        let root := returnDataPtr callbackPtr data.size
        have hroot : root.toNat = 1632 + 160 * market.collaterals.length +
            paddedSize data.size := by
          rw [returnDataPtr_toNat hdataFit, hcallbackPtr, returnDataAllocation_eq]
          omega
        refine Or.inr ⟨_, hdecode.trans hdo, hsmall, hratOff, _, callbackPtr, root,
          aw3, k3, C3, hcallbackPtr, hroot,
          offerDecodedMemory_stored hmarket (by decide) hcanon hd hdataFit,
          offerDecodedMemory_free (by omega) hd, offerDecodedMemory_size hd hdataFit,
          offerDecodedMemory_low hk2 (by decide)
            (by rw [memoryWordSnapshot_length]) (by omega) hd, ?_, rd3⟩
        simpa only [Nat.zero_add] using ha3
  · refine Or.inl ⟨?_, ?_⟩
    · intro offer hd
      exact False.elim (hsmall (decodeCalldataOffer_success hd).2.1)
    · exact midnightMarketCalldataHuge (by simp only [List.length_cons]; omega)
        hsize (by omega) (by rw [hhead]; omega) (by decide)
        (offerPrepareMemory_free mem) rd1

end Benchmarks.Midnight
