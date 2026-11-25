import Benchmarks.Midnight.OfferEncodeFirst
import Benchmarks.Midnight.Uint128Arithmetic

variable {fork : Ethereum.Fork}

/-! The remaining scalar fields and return from the offer ABI encoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def OfferData.encodeLastFour (offer : OfferData) : List UInt256 :=
  [UInt256.ofNat offer.receiverIfMakerIsSeller.val, UInt256.ofNat offer.ratifier.val,
    offer.reduceOnly, offer.maxUnits]

def OfferData.encodeLastWords (offer : OfferData) : List UInt256 :=
  offer.encodeLastFour ++ [offer.maxAssets, offer.continuousFeeCap]

def offerEncodeLastRaw (mem : ByteArray) (ptr output : UInt256) : ByteArray :=
  let m1 := writeWord mem (output + UInt256.ofNat 288).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 288) mem) solcAddrMask)
  let m2 := writeWord m1 (output + UInt256.ofNat 320).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 320) m1) solcAddrMask)
  let m3 := writeWord m2 (output + UInt256.ofNat 352).toNat
    (UInt256.isZero (UInt256.isZero (memLoad (ptr + UInt256.ofNat 352) m2)))
  writeWord m3 (output + UInt256.ofNat 384).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 384) m3) uint128Mask)

theorem offerEncodeLastBlock_memory (mem : ByteArray) (ptr output : UInt256) :
    midnightBlocks.midnight_block_20270_memory (mem := mem) (x3 := output) (x4 := ptr) =
      offerEncodeLastRaw mem ptr output := by
  simp only [midnightBlocks.midnight_block_20270_memory, addressMask_computed, uint128Mask_computed]
  rfl

theorem offerEncodeLastRaw_eq {mem : ByteArray} {ptr output marketPtr callbackPtr : UInt256}
    (offer : OfferData) (hm : MemoryWords mem ptr.toNat (offer.words marketPtr callbackPtr))
    (hc : OfferCanonical offer) (hbelow : ptr.toNat + 480 ≤ output.toNat)
    (hout : output.toNat + 416 < UInt256.size) :
    offerEncodeLastRaw mem ptr output =
      writeWordArray mem (output.toNat + 288) offer.encodeLastFour := by
  have hlen : (offer.words marketPtr callbackPtr).length = 15 := rfl
  have add (off : Nat) (ho : off ≤ 384) :
      (output + UInt256.ofNat off).toNat = output.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hr := solcAddrMask_clean (addressWord_canonical offer.receiverIfMakerIsSeller)
  have ha := solcAddrMask_clean (addressWord_canonical offer.ratifier)
  have hb := (boolWordClean_iff offer.reduceOnly).mpr hc.reduceOnly
  have hu := uint128Mask_clean hc.maxUnits
  have h1 : memLoad (ptr + UInt256.ofNat 288) mem = UInt256.ofNat offer.receiverIfMakerIsSeller.val :=
    hm.load_offset ⟨9, by change 9 < 15; decide⟩ rfl
  let m1 := writeWord mem (output + UInt256.ofNat 288).toNat (UInt256.ofNat offer.receiverIfMakerIsSeller.val)
  have hm1 : MemoryWords m1 ptr.toNat (offer.words marketPtr callbackPtr) :=
    hm.writeWord _ (Or.inl (by rw [add 288 (by decide), hlen]; omega))
  have h2 : memLoad (ptr + UInt256.ofNat 320) m1 = UInt256.ofNat offer.ratifier.val :=
    hm1.load_offset ⟨10, by change 10 < 15; decide⟩ rfl
  let m2 := writeWord m1 (output + UInt256.ofNat 320).toNat (UInt256.ofNat offer.ratifier.val)
  have hm2 : MemoryWords m2 ptr.toNat (offer.words marketPtr callbackPtr) :=
    hm1.writeWord _ (Or.inl (by rw [add 320 (by decide), hlen]; omega))
  have h3 : memLoad (ptr + UInt256.ofNat 352) m2 = offer.reduceOnly :=
    hm2.load_offset ⟨11, by change 11 < 15; decide⟩ rfl
  let m3 := writeWord m2 (output + UInt256.ofNat 352).toNat (offer.reduceOnly)
  have hm3 : MemoryWords m3 ptr.toNat (offer.words marketPtr callbackPtr) :=
    hm2.writeWord _ (Or.inl (by rw [add 352 (by decide), hlen]; omega))
  have h4 : memLoad (ptr + UInt256.ofNat 384) m3 = offer.maxUnits :=
    hm3.load_offset ⟨12, by change 12 < 15; decide⟩ rfl
  dsimp only [m1, m2, m3] at h2 h3 h4
  unfold offerEncodeLastRaw
  dsimp only
  rw [h1, hr, h2, ha, h3, hb, h4, hu]
  simp only [OfferData.encodeLastFour, writeWordArray, add 288 (by decide), add 320 (by decide),
    add 352 (by decide), add 384 (by decide), Nat.add_assoc, Nat.reduceAdd]

theorem offerEncodeLastBlock_stack {mem : ByteArray}
    {ptr output marketPtr callbackPtr finish x1 x2 : UInt256} (R : List UInt256)
    (offer : OfferData) (hm : MemoryWords mem ptr.toNat (offer.words marketPtr callbackPtr))
    (hc : OfferCanonical offer) (hbelow : ptr.toNat + 480 ≤ output.toNat)
    (hout : output.toNat + 416 < UInt256.size) :
    midnightBlocks.midnight_block_20270_stack (mem := mem) (x0 := finish) (x1 := x1)
      (x2 := x2) (x3 := output) (x4 := ptr) (R := R) =
      offer.maxAssets :: ptr :: x1 :: x2 :: output :: finish :: R := by
  simp only [midnightBlocks.midnight_block_20270_stack, addressMask_computed, uint128Mask_computed]
  change UInt256.land (memLoad (ptr + UInt256.ofNat 416) (offerEncodeLastRaw mem ptr output))
    uint128Mask :: _ = _
  rw [offerEncodeLastRaw_eq offer hm hc hbelow hout]
  have hm' := hm.writeWords offer.encodeLastFour (off := output.toNat + 288)
    (Or.inl (by change ptr.toNat + 32 * 15 ≤ _; omega))
  have hx : memLoad (ptr + UInt256.ofNat 416)
      (writeWordArray mem (output.toNat + 288) offer.encodeLastFour) = offer.maxAssets :=
    hm'.load_offset ⟨13, by change 13 < 15; decide⟩ rfl
  rw [hx, uint128Mask_clean hc.maxAssets]

set_option maxHeartbeats 800000 in
theorem midnightOfferEncodeLast_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr output marketPtr callbackPtr finish ret : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (offer : OfferData)
    (hstack : R.length + 9 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (offer.words marketPtr callbackPtr))
    (hc : OfferCanonical offer) (hbelow : ptr.toNat + 480 ≤ output.toNat)
    (hout : output.toNat + 480 < UInt256.size)
    (hret : (D_J midnightBytecode 0).contains ret = true) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨20270⟩
      (finish :: ⟨448⟩ :: ⟨448⟩ :: output :: ptr :: ret :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit
        (writeWordArray mem (output.toNat + 288) offer.encodeLastWords) aw' C' ∧
      RD fork midnightBytecode I g s0 ret (finish :: R)
        (writeWordArray mem (output.toNat + 288) offer.encodeLastWords) aw' rdata σ k' C' := by
  have add (off : Nat) (ho : off ≤ 448) :
      (output + UInt256.ofNat off).toNat = output.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have cover (active : UInt256) (hcovered : MemoryCovered mem active) :
      MemoryCovered (writeWordArray mem (output.toNat + 288) offer.encodeLastFour)
        (M active (output + UInt256.ofNat 384) ⟨32⟩) := by
    have hs := hcovered.expand (output + UInt256.ofNat 384) ⟨32⟩
    have hl := memoryWords_covers active (output + UInt256.ofNat 384) ⟨32⟩ (by decide)
    rw [add 384 (by decide)] at hl
    unfold MemoryCovered at hs ⊢
    simp only [OfferData.encodeLastFour, writeWordArray, writeWord_sparse_size,
      Nat.add_assoc, Nat.reduceAdd]
    change output.toNat + 384 + 32 ≤ _ at hl
    omega
  have rd1 := midnightBlocks.midnight_block_20270 (by simp only [List.length_cons]; omega) rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    constructor
    · have hp0 : Cₘ aw + credit ≤ (C + 190) + 79 :=
        ha.paid.trans (Nat.add_le_add_right (Nat.le_add_right C 190) 79)
      have hp1 := memoryCreditPaid_expand (ptr + UInt256.ofNat 288) ⟨32⟩ hp0
      have hp2 := memoryCreditPaid_expand (output + UInt256.ofNat 288) ⟨32⟩ hp1
      have hp3 := memoryCreditPaid_expand (ptr + UInt256.ofNat 320) ⟨32⟩ hp2
      have hp4 := memoryCreditPaid_expand (output + UInt256.ofNat 320) ⟨32⟩ hp3
      have hp5 := memoryCreditPaid_expand (ptr + UInt256.ofNat 352) ⟨32⟩ hp4
      have hp6 := memoryCreditPaid_expand (output + UInt256.ofNat 352) ⟨32⟩ hp5
      have hp7 := memoryCreditPaid_expand (ptr + UInt256.ofNat 384) ⟨32⟩ hp6
      have hp8 := memoryCreditPaid_expand (output + UInt256.ofNat 384) ⟨32⟩ hp7
      have hp9 := memoryCreditPaid_expand (ptr + UInt256.ofNat 416) ⟨32⟩ hp8
      simpa only [Nat.add_assoc] using hp9
    · rw [offerEncodeLastBlock_memory, offerEncodeLastRaw_eq offer hm hc hbelow (by omega)]
      apply MemoryCovered.expand
      apply cover
      repeat' apply MemoryCovered.expand
      exact ha.covered)
  simp only [offerEncodeLastBlock_memory,
    offerEncodeLastRaw_eq offer hm hc hbelow (by omega),
    offerEncodeLastBlock_stack _ offer hm hc hbelow (by omega)] at rd1 ha1
  have hm4 := hm.writeWords offer.encodeLastFour (off := output.toNat + 288)
    (Or.inl (by change ptr.toNat + 32 * 15 ≤ _; omega))
  have hm5 := hm4.writeWord offer.maxAssets (off := (output + UInt256.ofNat 416).toNat)
    (Or.inl (by rw [add 416 (by decide)]; change ptr.toNat + 32 * 15 ≤ _; omega))
  have hf : memLoad (ptr + UInt256.ofNat 448)
      (writeWord (writeWordArray mem (output.toNat + 288) offer.encodeLastFour)
        (output + UInt256.ofNat 416).toNat offer.maxAssets) = offer.continuousFeeCap :=
    hm5.load_offset ⟨14, by change 14 < 15; decide⟩ rfl
  have rd2 := midnightBlocks.midnight_block_20364 (x2 := UInt256.ofNat 448)
    (x3 := UInt256.ofNat 448) hstack hret rd1
  have ha2 := memoryFundingAt (credit := credit) rd2 (by
    unfold midnightBlocks.midnight_block_20364_memory
    memory_fund ha1)
  have hr := And.intro ha2 rd2
  simp only [midnightBlocks.midnight_block_20364_stack,
    midnightBlocks.midnight_block_20364_memory, writeWord_fold, hf] at hr
  simp only [add 416 (by decide), add 448 (by decide)] at hr
  simp only [OfferData.encodeLastWords, writeWordArray_append]
  change ∃ aw' k' C', MemoryFunding credit
    (writeWord (writeWord (writeWordArray mem (output.toNat + 288) offer.encodeLastFour)
      (output.toNat + 416) offer.maxAssets) (output.toNat + 448) offer.continuousFeeCap) aw' C' ∧ _
  exact ⟨_, _, _, hr⟩

end Benchmarks.Midnight
