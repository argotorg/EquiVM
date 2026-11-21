import Benchmarks.Midnight.RatifierPrepare
import Benchmarks.Midnight.OfferEncodeRead

/-! The preserved regions and selector of the ratifier's runtime call buffer. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: a preserved word preserves every shorter prefix of that word.
theorem MemoryPrefix.read_short {before after : ByteArray} {limit off len : Nat}
    (h : MemoryPrefix before after limit) (hlo : 96 ≤ off) (hlen : len ≤ 32)
    (hlim : off + 32 ≤ limit) (hin : off + 32 ≤ before.size) :
    after.readWithPadding off len = before.readWithPadding off len := by
  by_cases hz : len = 0
  · simp only [hz, byteArray_readWithPadding_zero]
  have hh := congrArg (fun bytes : ByteArray ↦ bytes.extract 0 len) (h.read off hlo hlim hin)
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by decide) (hin.trans h.size),
    readWithPadding_eq_extract_unbounded _ _ _ (by decide) hin] at hh
  simp only [extract_extract_BA, Nat.add_zero, min_eq_left (by omega : off + len ≤ off + 32)] at hh
  rw [readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by have hs := h.size; omega),
    readWithPadding_eq_extract_unbounded _ _ _ (by omega) (by omega)]
  exact hh

theorem ratifierInputHead_selector (mem : ByteArray) (root : Nat) :
    (ratifierInputHead mem root).readWithPadding root 4 =
      (⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ : ByteArray) := by
  have hr := writeWord_sparse_read_window mem root 0 4
    (UInt256.ofNat (574377686 * 2^224)) (by decide) (by decide) (by decide)
  have hs : (UInt256.ofNat (574377686 * 2^224)).toByteArray.extract 0 4 =
      (⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ : ByteArray) := by decide +kernel
  simp only [Nat.add_zero, Nat.zero_add, hs] at hr
  unfold ratifierInputHead
  rw [writeWord_sparse_read_preserved_len _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) (Or.inl le_rfl) (by decide) (by decide), hr]

def ratifierInputWords (offer : OfferData) (taker : AccountAddress) : List UInt256 :=
  [UInt256.ofNat 96, UInt256.ofNat (96 + offerEncodedSize offer), UInt256.ofNat taker.val]

set_option maxHeartbeats 800000 in
theorem ratifierInputMemory_regions {mem data : ByteArray} {root callbackPtr ratifierPtr : UInt256}
    (offer : OfferData) (taker : AccountAddress)
    (hc : MemoryByteString mem callbackPtr offer.callbackData)
    (hb : MemoryByteString mem ratifierPtr data)
    (hcpad : paddedSize offer.callbackData.size < 2^64) (hbpad : paddedSize data.size < 2^64)
    (hcbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat)
    (hbbelow : ratifierPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hout : root.toNat + ratifierCalldataSize offer data + 64 < UInt256.size) :
    let final := ratifierInputMemory mem root callbackPtr ratifierPtr offer data taker
    MemoryWords final (root.toNat + 4) (ratifierInputWords offer taker) ∧
      final.readWithPadding (root.toNat + 100) (offerEncodedSize offer) = offerEncodedBytes offer ∧
      MemoryByteString final (root + UInt256.ofNat (100 + offerEncodedSize offer)) data ∧
      MemoryPrefix mem final root.toNat ∧
      final.readWithPadding root.toNat 4 = (⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ : ByteArray) := by
  have hlo : 96 ≤ root.toNat := by have hl := hc.lower; omega
  have hpadded := nat_le_paddedSize data.size
  have h100 : (root + UInt256.ofNat 100).toNat = root.toNat + 100 :=
    uadd_word_ofNat_toNat _ _ (by unfold ratifierCalldataSize at hout; omega)
  have hdest : (root + UInt256.ofNat (100 + offerEncodedSize offer)).toNat =
      root.toNat + 100 + offerEncodedSize offer := by
    rw [uadd_word_ofNat_toNat _ _ (by unfold ratifierCalldataSize at hout; omega)]
    omega
  have hoff : (root + UInt256.ofNat 100).toNat + offerEncodedSize offer + 64 < UInt256.size := by
    rw [h100]
    unfold ratifierCalldataSize at hout
    omega
  have hcb : ((root + UInt256.ofNat 100) + UInt256.ofNat (offerCallbackOffset offer)).toNat =
      root.toNat + 100 + offerCallbackOffset offer := by
    rw [uadd_word_ofNat_toNat _ _ (by unfold offerEncodedSize at hoff; omega), h100]
  let head := ratifierInputHead mem root.toNat
  let encoded := offerEncodeMemory head callbackPtr (root + UInt256.ofNat 100) offer
  let offset := writeWord encoded (root.toNat + 36) (UInt256.ofNat (96 + offerEncodedSize offer))
  let bytes := memoryBytesEncodeMemory offset ratifierPtr.toNat
    (root.toNat + 100 + offerEncodedSize offer) data.size
  let final := writeWord bytes (root.toNat + 68) (UInt256.ofNat taker.val)
  have hp0 : MemoryPrefix mem head root.toNat := ratifierInputHead_prefix _ _
  have hc0 := hc.preserve hp0 hcbelow
  have hb0 := hb.preserve hp0 hbbelow
  obtain ⟨hw1, hc1, hp1, _⟩ := offerEncodeMemory_spec offer hc0 hcpad
    (output := root + UInt256.ofNat 100) (by rw [h100]; omega) hoff
  have hb1 := hb0.preserve hp1 (by rw [h100]; omega)
  have hp2 : MemoryPrefix encoded offset root.toNat :=
    memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega))
  have hb2 := hb1.preserve hp2 hbbelow
  have hsrc : ratifierPtr.toNat + 32 + data.size ≤ offset.size := by
    have hs := hb2.size
    omega
  have hp3 : MemoryPrefix offset bytes (root.toNat + 100 + offerEncodedSize offer) :=
    memoryBytesEncodeMemory_prefix _ _ _ _ _ hsrc le_rfl
  have hp4 : MemoryPrefix bytes final root.toNat :=
    memoryPrefix_writeWord _ _ _ _ (Or.inl (by omega))
  have hp : MemoryPrefix mem final root.toNat :=
    hp0.trans ((hp1.mono (by rw [h100]; omega)).trans
      (hp2.trans ((hp3.mono (by omega)).trans hp4)))
  have hwordslen : 32 * (offerEncodedPrefixWords offer).length = offerCallbackOffset offer + 32 := by
    rw [offerEncodedPrefixWords_length]
    unfold offerCallbackOffset
    omega
  have hw2 := hw1.writeWord (UInt256.ofNat (96 + offerEncodedSize offer))
    (off := root.toNat + 36) (Or.inr (by rw [h100]; omega))
  have hw3 := hw2.memoryBytesEncode (ptr := ratifierPtr.toNat)
    (output := root.toNat + 100 + offerEncodedSize offer) hsrc (by
      rw [h100, hwordslen]; unfold offerEncodedSize; omega)
  have hw4 := hw3.writeWord (UInt256.ofNat taker.val) (off := root.toNat + 68)
    (Or.inr (by rw [h100]))
  have hc2 := hc1.writeWord_below (UInt256.ofNat (96 + offerEncodedSize offer))
    (off := root.toNat + 36) (by rw [hcb]; omega) hcpad
  have hc3 := hc2.preserve hp3 (by rw [hcb]; unfold offerEncodedSize; omega)
  have hc4 := hc3.writeWord_below (UInt256.ofNat taker.val) (off := root.toNat + 68)
    (by rw [hcb]; omega) hcpad
  have hread : final.readWithPadding (root.toNat + 100) (offerEncodedSize offer) =
      offerEncodedBytes offer := by
    simpa only [h100] using offerEncodedRegions_read offer hw4 hc4 hoff
  have hb3 : MemoryByteString bytes (root + UInt256.ofNat (100 + offerEncodedSize offer)) data := by
    have hh := memoryBytesEncodeMemory_stored hb2
      (output := root + UInt256.ofNat (100 + offerEncodedSize offer))
      (by rw [hdest]; omega) (by rw [hdest]; omega)
      (by rw [hdest]; unfold ratifierCalldataSize at hout; omega)
    simpa only [hdest] using hh
  have hb4 := hb3.writeWord_below (UInt256.ofNat taker.val) (off := root.toNat + 68)
    (by rw [hdest]; omega) hbpad
  have hh0 : MemoryWords head (root.toNat + 4) [UInt256.ofNat 96] :=
    MemoryWords.of_writeWord _ _ _ (by unfold ratifierCalldataSize at hout; omega)
  have hh1 := hh0.preserve hp1.size (fun read hreadlo hhi ↦
    hp1.load read (by omega)
      (by rw [h100]; change read.toNat + 32 ≤ root.toNat + 4 + 32 * 1 at hhi; omega)
      (hhi.trans hh0.size))
  have hh2 : MemoryWords offset (root.toNat + 4)
      [UInt256.ofNat 96, UInt256.ofNat (96 + offerEncodedSize offer)] := by
    have hh := hh1.append_writeWordArray [UInt256.ofNat (96 + offerEncodedSize offer)]
      (by unfold ratifierCalldataSize at hout; change root.toNat + 4 + 32 * 2 < _; omega)
    change MemoryWords (writeWord encoded (root.toNat + 4 + 32)
      (UInt256.ofNat (96 + offerEncodedSize offer))) (root.toNat + 4)
      [UInt256.ofNat 96, UInt256.ofNat (96 + offerEncodedSize offer)] at hh
    rw [show root.toNat + 4 + 32 = root.toNat + 36 by omega] at hh
    exact hh
  have hh3 := hh2.memoryBytesEncode (ptr := ratifierPtr.toNat)
    (output := root.toNat + 100 + offerEncodedSize offer) hsrc (by
      change root.toNat + 4 + 32 * 2 ≤ _; omega)
  have hh4 : MemoryWords final (root.toNat + 4) (ratifierInputWords offer taker) := by
    have hh := hh3.append_writeWordArray [UInt256.ofNat taker.val]
      (by unfold ratifierCalldataSize at hout; change root.toNat + 4 + 32 * 3 < _; omega)
    change MemoryWords (writeWord bytes (root.toNat + 4 + 64) (UInt256.ofNat taker.val))
      (root.toNat + 4) (ratifierInputWords offer taker) at hh
    rw [show root.toNat + 4 + 64 = root.toNat + 68 by omega] at hh
    exact hh
  have hs0 : root.toNat + 32 ≤ head.size := by
    dsimp only [head, ratifierInputHead]
    rw [writeWord_sparse_size, writeWord_sparse_size]
    omega
  have hs1 : root.toNat + 32 ≤ encoded.size := hs0.trans hp1.size
  have hs2 : root.toNat + 32 ≤ offset.size := hs1.trans hp2.size
  have hs3 : root.toNat + 32 ≤ bytes.size := hs2.trans hp3.size
  have hsel1 : encoded.readWithPadding root.toNat 4 =
      (⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ : ByteArray) := by
    rw [hp1.read_short hlo (by decide) (by rw [h100]; omega) hs0,
      ratifierInputHead_selector]
  have hsel2 : offset.readWithPadding root.toNat 4 =
      (⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ : ByteArray) := by
    rw [show offset = _ from rfl,
      writeWord_sparse_read_preserved_len _ _ _ _ _ (by omega)
        (Or.inl (by omega)) (by decide) (by decide), hsel1]
  have hsel3 : bytes.readWithPadding root.toNat 4 =
      (⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ : ByteArray) := by
    rw [hp3.read_short hlo (by decide) (by omega) hs2, hsel2]
  have hsel4 : final.readWithPadding root.toNat 4 =
      (⟨#[0x22, 0x3c, 0x4e, 0xd6]⟩ : ByteArray) := by
    rw [show final = _ from rfl,
      writeWord_sparse_read_preserved_len _ _ _ _ _ (by omega)
        (Or.inl (by omega)) (by decide) (by decide), hsel3]
  exact ⟨hh4, hread, hb4, hp, hsel4⟩

theorem ratifierInputMemory_read {mem data : ByteArray} {root callbackPtr ratifierPtr : UInt256}
    (offer : OfferData) (taker : AccountAddress)
    (hc : MemoryByteString mem callbackPtr offer.callbackData)
    (hb : MemoryByteString mem ratifierPtr data)
    (hcpad : paddedSize offer.callbackData.size < 2^64) (hbpad : paddedSize data.size < 2^64)
    (hcbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat)
    (hbbelow : ratifierPtr.toNat + 32 + paddedSize data.size ≤ root.toNat)
    (hout : root.toNat + ratifierCalldataSize offer data + 64 < UInt256.size) :
    let final := ratifierInputMemory mem root callbackPtr ratifierPtr offer data taker
    root.toNat + ratifierCalldataSize offer data ≤ final.size ∧
      final.readWithPadding root.toNat (ratifierCalldataSize offer data) =
        ratifierCalldata offer data taker ∧ MemoryPrefix mem final root.toNat := by
  obtain ⟨hw, ho, hb, hp, hs⟩ := ratifierInputMemory_regions offer taker hc hb hcpad hbpad
    hcbelow hbbelow hout
  have hdest : (root + UInt256.ofNat (100 + offerEncodedSize offer)).toNat =
      root.toNat + 100 + offerEncodedSize offer := by
    rw [uadd_word_ofNat_toNat _ _ (by unfold ratifierCalldataSize at hout; omega)]
    omega
  have hsize := hb.size
  rw [hdest] at hsize
  have hcovered : root.toNat + ratifierCalldataSize offer data ≤
      (ratifierInputMemory mem root callbackPtr ratifierPtr offer data taker).size := by
    unfold ratifierCalldataSize
    omega
  refine ⟨hcovered, ?_, hp⟩
  have hhead := hw.read
  change (ratifierInputMemory mem root callbackPtr ratifierPtr offer data taker).readWithPadding
    (root.toNat + 4) 96 = wordArrayBytes (ratifierInputWords offer taker) at hhead
  have hlength := hb.headerWords.read
  change (ratifierInputMemory mem root callbackPtr ratifierPtr offer data taker).readWithPadding
    (root + UInt256.ofNat (100 + offerEncodedSize offer)).toNat 32 =
      wordArrayBytes [UInt256.ofNat data.size] at hlength
  rw [hdest] at hlength
  have hdata := hb.payload
  rw [hdest] at hdata
  have he : ratifierCalldataSize offer data = 4 + (96 +
      (offerEncodedSize offer + (32 + paddedSize data.size))) := by
    unfold ratifierCalldataSize
    omega
  rw [he, readWithPadding_split_inbounds _ _ _ _ (by omega), hs,
    readWithPadding_split_inbounds _ _ _ _ (by omega), hhead,
    show root.toNat + 4 + 96 = root.toNat + 100 by omega,
    readWithPadding_split_inbounds _ _ _ _ (by omega), ho,
    readWithPadding_split_inbounds _ _ _ _ hsize, hlength, hdata]
  simp only [ratifierCalldata, ratifierInputWords, wordArrayBytes, ByteArray.append_empty,
    ByteArray.append_assoc]

end Benchmarks.Midnight
