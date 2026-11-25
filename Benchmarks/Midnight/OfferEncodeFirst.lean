import Benchmarks.Midnight.OfferCanonical
import Benchmarks.Midnight.OfferHeapMemory
import Benchmarks.Midnight.MemoryCreditPaid
import Benchmarks.Midnight.RuntimeBlocks_077

variable {fork : Ethereum.Fork}

/-! The first six scalar fields of an ABI-encoded offer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

def OfferData.encodeFirstWords (offer : OfferData) : List UInt256 :=
  [offer.buy, UInt256.ofNat offer.maker.val, offer.start, offer.expiry, offer.tick, offer.group]

def offerEncodeFirstRaw (mem : ByteArray) (ptr output : UInt256) : ByteArray :=
  let m1 := writeWord mem (output + UInt256.ofNat 32).toNat
    (UInt256.isZero (UInt256.isZero (memLoad (ptr + UInt256.ofNat 32) mem)))
  let m2 := writeWord m1 (output + UInt256.ofNat 64).toNat
    (UInt256.land (memLoad (ptr + UInt256.ofNat 64) m1) solcAddrMask)
  let m3 := writeWord m2 (output + UInt256.ofNat 96).toNat (memLoad (ptr + UInt256.ofNat 96) m2)
  let m4 := writeWord m3 (output + UInt256.ofNat 128).toNat (memLoad (ptr + UInt256.ofNat 128) m3)
  let m5 := writeWord m4 (output + UInt256.ofNat 160).toNat (memLoad (ptr + UInt256.ofNat 160) m4)
  writeWord m5 (output + UInt256.ofNat 192).toNat (memLoad (ptr + UInt256.ofNat 192) m5)

theorem offerEncodeFirstBlock_memory (mem : ByteArray) (ptr output : UInt256) :
    midnightBlocks.midnight_block_20160_memory (mem := mem) (x4 := output) (x5 := ptr) =
      offerEncodeFirstRaw mem ptr output := by
  simp only [midnightBlocks.midnight_block_20160_memory, addressMask_computed]
  rfl

theorem offerEncodeFirstRaw_eq {mem : ByteArray} {ptr output marketPtr callbackPtr : UInt256}
    (offer : OfferData) (hm : MemoryWords mem ptr.toNat (offer.words marketPtr callbackPtr))
    (hc : OfferCanonical offer) (hbelow : ptr.toNat + 480 ≤ output.toNat)
    (hout : output.toNat + 224 < UInt256.size) :
    offerEncodeFirstRaw mem ptr output =
      writeWordArray mem (output.toNat + 32) offer.encodeFirstWords := by
  have hlen : (offer.words marketPtr callbackPtr).length = 15 := rfl
  have add (off : Nat) (ho : off ≤ 192) :
      (output + UInt256.ofNat off).toNat = output.toNat + off :=
    uadd_word_ofNat_toNat _ _ (by omega)
  have hb := (boolWordClean_iff offer.buy).mpr hc.buy
  have ha := solcAddrMask_clean (addressWord_canonical offer.maker)
  have h1 : memLoad (ptr + UInt256.ofNat 32) mem = offer.buy :=
    hm.load_offset ⟨1, by change 1 < 15; decide⟩ rfl
  let m1 := writeWord mem (output + UInt256.ofNat 32).toNat (offer.buy)
  have hm1 : MemoryWords m1 ptr.toNat (offer.words marketPtr callbackPtr) :=
    hm.writeWord _ (Or.inl (by rw [add 32 (by decide), hlen]; omega))
  have h2 : memLoad (ptr + UInt256.ofNat 64) m1 = UInt256.ofNat offer.maker.val :=
    hm1.load_offset ⟨2, by change 2 < 15; decide⟩ rfl
  let m2 := writeWord m1 (output + UInt256.ofNat 64).toNat (UInt256.ofNat offer.maker.val)
  have hm2 : MemoryWords m2 ptr.toNat (offer.words marketPtr callbackPtr) :=
    hm1.writeWord _ (Or.inl (by rw [add 64 (by decide), hlen]; omega))
  have h3 : memLoad (ptr + UInt256.ofNat 96) m2 = offer.start :=
    hm2.load_offset ⟨3, by change 3 < 15; decide⟩ rfl
  let m3 := writeWord m2 (output + UInt256.ofNat 96).toNat (offer.start)
  have hm3 : MemoryWords m3 ptr.toNat (offer.words marketPtr callbackPtr) :=
    hm2.writeWord _ (Or.inl (by rw [add 96 (by decide), hlen]; omega))
  have h4 : memLoad (ptr + UInt256.ofNat 128) m3 = offer.expiry :=
    hm3.load_offset ⟨4, by change 4 < 15; decide⟩ rfl
  let m4 := writeWord m3 (output + UInt256.ofNat 128).toNat (offer.expiry)
  have hm4 : MemoryWords m4 ptr.toNat (offer.words marketPtr callbackPtr) :=
    hm3.writeWord _ (Or.inl (by rw [add 128 (by decide), hlen]; omega))
  have h5 : memLoad (ptr + UInt256.ofNat 160) m4 = offer.tick :=
    hm4.load_offset ⟨5, by change 5 < 15; decide⟩ rfl
  let m5 := writeWord m4 (output + UInt256.ofNat 160).toNat (offer.tick)
  have hm5 : MemoryWords m5 ptr.toNat (offer.words marketPtr callbackPtr) :=
    hm4.writeWord _ (Or.inl (by rw [add 160 (by decide), hlen]; omega))
  have h6 : memLoad (ptr + UInt256.ofNat 192) m5 = offer.group :=
    hm5.load_offset ⟨6, by change 6 < 15; decide⟩ rfl
  dsimp only [m1, m2, m3, m4, m5] at h2 h3 h4 h5 h6
  unfold offerEncodeFirstRaw
  dsimp only
  rw [h1, hb, h2, ha, h3, h4, h5, h6]
  simp only [OfferData.encodeFirstWords, writeWordArray, add 32 (by decide), add 64 (by decide),
    add 96 (by decide), add 128 (by decide), add 160 (by decide), add 192 (by decide),
    Nat.add_assoc, Nat.reduceAdd]

set_option maxHeartbeats 800000 in
theorem midnightOfferEncodeFirst_funded {credit : Nat} {I : ExecutionEnv} {g : Sat256}
    {s0 : State} {mem rdata : ByteArray} {aw ptr output marketPtr callbackPtr finish : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256} (offer : OfferData)
    (hstack : R.length + 9 ≤ 1024)
    (hm : MemoryWords mem ptr.toNat (offer.words marketPtr callbackPtr))
    (hc : OfferCanonical offer) (hbelow : ptr.toNat + 480 ≤ output.toNat)
    (hout : output.toNat + 224 < UInt256.size) (ha : MemoryFunding credit mem aw C)
    (rd : RD fork midnightBytecode I g s0 ⟨20160⟩
      (finish :: ⟨20270⟩ :: ⟨448⟩ :: ⟨448⟩ :: output :: ptr :: R) mem aw rdata σ k C) :
    ∃ aw' k' C', MemoryFunding credit
        (writeWordArray mem (output.toNat + 32) offer.encodeFirstWords) aw' C' ∧
      RD fork midnightBytecode I g s0 ⟨20243⟩
        (ptr :: ⟨224⟩ :: solcAddrMask :: finish :: ⟨20270⟩ :: ⟨448⟩ :: ⟨448⟩ :: output :: ptr :: R)
        (writeWordArray mem (output.toNat + 32) offer.encodeFirstWords) aw' rdata σ k' C' := by
  have cover (active : UInt256) (hcovered : MemoryCovered mem active) :
      MemoryCovered (writeWordArray mem (output.toNat + 32) offer.encodeFirstWords)
        (M active (output + UInt256.ofNat 192) ⟨32⟩) := by
    have hs := hcovered.expand (output + UInt256.ofNat 192) ⟨32⟩
    have hl := memoryWords_covers active (output + UInt256.ofNat 192) ⟨32⟩ (by decide)
    rw [uadd_word_ofNat_toNat _ _ (by omega)] at hl
    unfold MemoryCovered at hs ⊢
    simp only [OfferData.encodeFirstWords, writeWordArray, writeWord_sparse_size,
      Nat.add_assoc, Nat.reduceAdd]
    change output.toNat + 192 + 32 ≤ _ at hl
    omega
  have rd1 := midnightBlocks.midnight_block_20160 hstack rd
  have ha1 := memoryFundingAt (credit := credit) rd1 (by
    constructor
    · have hp0 : Cₘ aw + credit ≤ (C + 190) + 79 :=
        ha.paid.trans (Nat.add_le_add_right (Nat.le_add_right C 190) 79)
      have hp1 := memoryCreditPaid_expand (ptr + UInt256.ofNat 32) ⟨32⟩ hp0
      have hp2 := memoryCreditPaid_expand (output + UInt256.ofNat 32) ⟨32⟩ hp1
      have hp3 := memoryCreditPaid_expand (ptr + UInt256.ofNat 64) ⟨32⟩ hp2
      have hp4 := memoryCreditPaid_expand (output + UInt256.ofNat 64) ⟨32⟩ hp3
      have hp5 := memoryCreditPaid_expand (ptr + UInt256.ofNat 96) ⟨32⟩ hp4
      have hp6 := memoryCreditPaid_expand (output + UInt256.ofNat 96) ⟨32⟩ hp5
      have hp7 := memoryCreditPaid_expand (ptr + UInt256.ofNat 128) ⟨32⟩ hp6
      have hp8 := memoryCreditPaid_expand (output + UInt256.ofNat 128) ⟨32⟩ hp7
      have hp9 := memoryCreditPaid_expand (ptr + UInt256.ofNat 160) ⟨32⟩ hp8
      have hp10 := memoryCreditPaid_expand (output + UInt256.ofNat 160) ⟨32⟩ hp9
      have hp11 := memoryCreditPaid_expand (ptr + UInt256.ofNat 192) ⟨32⟩ hp10
      have hp12 := memoryCreditPaid_expand (output + UInt256.ofNat 192) ⟨32⟩ hp11
      simpa only [Nat.add_assoc] using hp12
    · rw [offerEncodeFirstBlock_memory, offerEncodeFirstRaw_eq offer hm hc hbelow hout]
      apply cover
      repeat' apply MemoryCovered.expand
      exact ha.covered)
  have hr := And.intro ha1 rd1
  simp only [midnightBlocks.midnight_block_20160_stack, addressMask_computed,
    offerEncodeFirstBlock_memory, offerEncodeFirstRaw_eq offer hm hc hbelow hout] at hr
  exact ⟨_, _, _, hr⟩

end Benchmarks.Midnight
