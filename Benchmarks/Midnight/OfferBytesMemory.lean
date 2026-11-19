import Benchmarks.Midnight.OfferBytesSource
import Benchmarks.Midnight.OfferEncodeRead

/-! The allocated offer byte buffer and preservation of the caller's heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def offerBytesDataMemory (mem : ByteArray) (root callbackPtr : UInt256)
    (offer : OfferData) : ByteArray :=
  offerEncodeMemory (writeWord mem (root.toNat + 32) (UInt256.ofNat 32)) callbackPtr
    (root + UInt256.ofNat 64) offer

def offerBytesMemory (mem : ByteArray) (root callbackPtr : UInt256)
    (offer : OfferData) : ByteArray :=
  writeWord (writeWord (offerBytesDataMemory mem root callbackPtr offer) root.toNat
    (UInt256.ofNat (offerBytesSize offer))) 64 (root + UInt256.ofNat (offerBytesSize offer + 32))

theorem offerBytesDataMemory_spec {mem : ByteArray} {root callbackPtr : UInt256} (offer : OfferData)
    (hc : MemoryByteString mem callbackPtr offer.callbackData)
    (hpad : paddedSize offer.callbackData.size < 2^64)
    (hbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat)
    (hb : root.toNat + offerEncodedSize offer + 128 < UInt256.size) :
    MemoryPrefix mem (offerBytesDataMemory mem root callbackPtr offer) root.toNat ∧
      root.toNat + 32 + offerBytesSize offer ≤
        (offerBytesDataMemory mem root callbackPtr offer).size ∧
      (offerBytesDataMemory mem root callbackPtr offer).readWithPadding (root.toNat + 32)
        (offerBytesSize offer) = offerBytes offer := by
  have hroot : 96 ≤ root.toNat := by have h := hc.lower; omega
  have h64 : (root + UInt256.ofNat 64).toNat = root.toNat + 64 :=
    uadd_word_ofNat_toNat _ _ (by omega)
  let head := writeWord mem (root.toNat + 32) (UInt256.ofNat 32)
  have hp0 := memoryPrefix_writeWord mem (root.toNat + 32) root.toNat (UInt256.ofNat 32)
    (Or.inl (by omega))
  have hc0 : MemoryByteString head callbackPtr offer.callbackData := hc.preserve hp0 hbelow
  obtain ⟨hw, hc1, hp1, _⟩ := offerEncodeMemory_spec (output := root + UInt256.ofNat 64)
    offer hc0 hpad (by rw [h64]; omega) (by rw [h64]; omega)
  have hcb : ((root + UInt256.ofNat 64) + UInt256.ofNat (offerCallbackOffset offer)).toNat =
      root.toNat + 64 + offerCallbackOffset offer := by
    rw [uadd_word_ofNat_toNat _ _ (by
      rw [h64]; unfold offerEncodedSize at hb; omega), h64]
  have hsize : root.toNat + 32 + offerBytesSize offer ≤
      (offerBytesDataMemory mem root callbackPtr offer).size := by
    have hh := hc1.size
    rw [hcb] at hh
    unfold offerBytesSize offerEncodedSize
    exact Nat.le_trans (by omega) hh
  refine ⟨hp0.trans (hp1.mono (by rw [h64]; omega)), hsize, ?_⟩
  have hh : MemoryWords head (root.toNat + 32) [UInt256.ofNat 32] :=
    MemoryWords.of_writeWordArray mem (root.toNat + 32) [UInt256.ofNat 32] (by
      change root.toNat + 32 + 32 * 1 < UInt256.size; omega) (by simp)
  have hh1 : MemoryWords (offerBytesDataMemory mem root callbackPtr offer)
      (root.toNat + 32) [UInt256.ofNat 32] := by
    apply hh.preserve hp1.size
    intro word hlo hhi
    apply hp1.load word (by omega) _ (hhi.trans hh.size)
    rw [h64]
    simpa only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.mul_one, Nat.add_assoc] using hhi
  have hread := offerEncodedRegions_read offer hw hc1 (by rw [h64]; omega)
  rw [h64] at hread
  change (offerBytesDataMemory mem root callbackPtr offer).readWithPadding (root.toNat + 64)
    (offerEncodedSize offer) = offerEncodedBytes offer at hread
  rw [offerBytesSize, readWithPadding_split_inbounds _ (root.toNat + 32) 32
    (offerEncodedSize offer) (by unfold offerBytesSize at hsize; omega)]
  have hheader := hh1.read
  simp only [List.length_cons, List.length_nil, Nat.reduceAdd, Nat.mul_one,
    wordArrayBytes, ByteArray.append_empty] at hheader
  rw [hheader, show root.toNat + 32 + 32 = root.toNat + 64 by omega, hread]
  rfl

theorem offerBytesMemory_prefix {mem : ByteArray} {root callbackPtr : UInt256} (offer : OfferData)
    (hc : MemoryByteString mem callbackPtr offer.callbackData)
    (hpad : paddedSize offer.callbackData.size < 2^64)
    (hbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat)
    (hb : root.toNat + offerEncodedSize offer + 128 < UInt256.size) :
    MemoryPrefix mem (offerBytesMemory mem root callbackPtr offer) root.toNat :=
  (((offerBytesDataMemory_spec offer hc hpad hbelow hb).1).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inl le_rfl))).trans
    (memoryPrefix_writeWord _ _ _ _ (Or.inr (by decide)))

theorem offerBytesMemory_free (mem : ByteArray) (root callbackPtr : UInt256) (offer : OfferData) :
    memLoad (UInt256.ofNat 64) (offerBytesMemory mem root callbackPtr offer) =
      root + UInt256.ofNat (offerBytesSize offer + 32) := memLoad_writeWord _ _ _

theorem offerBytesMemory_stored {mem : ByteArray} {root callbackPtr : UInt256} (offer : OfferData)
    (hc : MemoryByteString mem callbackPtr offer.callbackData)
    (hpad : paddedSize offer.callbackData.size < 2^64)
    (hbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat)
    (hb : root.toNat + offerEncodedSize offer + 128 < UInt256.size)
    (hfit : root.toNat + offerBytesSize offer + 32 < 2^64) :
    MemoryByteString (offerBytesMemory mem root callbackPtr offer) root (offerBytes offer) := by
  have hroot : 96 ≤ root.toNat := by have h := hc.lower; omega
  obtain ⟨_, hsize, hread⟩ := offerBytesDataMemory_spec offer hc hpad hbelow hb
  have hbs : paddedSize (offerBytes offer).size = offerBytesSize offer := by
    rw [offerBytes_size, offerBytesSize_padded]
  have hh : MemoryByteString
      (writeWord (offerBytesDataMemory mem root callbackPtr offer) root.toNat
        (UInt256.ofNat (offerBytesSize offer))) root (offerBytes offer) := by
    refine ⟨hroot, by rw [offerBytes_size]; omega, by rw [hbs]; unfold offerBytesSize; omega,
      ?_, ?_, ?_⟩
    · rw [hbs, writeWord_sparse_size]; omega
    · rw [offerBytes_size]; exact memLoad_writeWord _ _ _
    · rw [hbs, offerBytes_size, Nat.sub_self,
        show ByteArray.zeroes 0 = ByteArray.empty from
          ByteArray.size_eq_zero_iff.mp (ByteArray_zeroes_size 0), ByteArray.append_empty]
      rw [writeWord_sparse_read_preserved_len _ _ _ _ _ hsize (Or.inr le_rfl)
        (by unfold offerBytesSize; omega) (by omega), hread]
  exact hh.writeWord_below _ (by omega) (by rw [hbs]; omega)

end Benchmarks.Midnight
