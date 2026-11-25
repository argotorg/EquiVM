import Benchmarks.Midnight.OfferEncodeMemory
import Benchmarks.Midnight.FlashLoanCallbackRead

/-! The runtime offer encoder's memory slice equals the source ABI value encoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem offerEncodedRegions_read {mem : ByteArray} {output : UInt256} (offer : OfferData)
    (hw : MemoryWords mem output.toNat (offerEncodedPrefixWords offer))
    (hb : MemoryByteString mem
      (output + UInt256.ofNat (offerCallbackOffset offer)) offer.callbackData)
    (hout : output.toNat + offerEncodedSize offer + 64 < UInt256.size) :
    mem.readWithPadding output.toNat (offerEncodedSize offer) = offerEncodedBytes offer := by
  have hdest : (output + UInt256.ofNat (offerCallbackOffset offer)).toNat =
      output.toNat + offerCallbackOffset offer :=
    uadd_word_ofNat_toNat _ _ (by unfold offerEncodedSize at hout; omega)
  have hs := hb.size
  rw [hdest] at hs
  have hlen : offerEncodedSize offer = 32 * (offerEncodedPrefixWords offer).length +
      paddedSize offer.callbackData.size := by
    rw [offerEncodedPrefixWords_length]
    unfold offerEncodedSize offerCallbackOffset
    omega
  have hstart : output.toNat + 32 * (offerEncodedPrefixWords offer).length =
      (output + UInt256.ofNat (offerCallbackOffset offer)).toNat + 32 := by
    rw [hdest, offerEncodedPrefixWords_length]
    unfold offerCallbackOffset
    omega
  rw [hlen, readWithPadding_split_inbounds _ _ _ _ (by rw [hstart, hdest]; exact hs),
    hw.read, hstart, hb.payload]
  simp only [offerEncodedPrefixWords, offerEncodedBytes, wordArrayBytes_append, wordArrayBytes,
    ByteArray.append_empty, ByteArray.append_assoc]

theorem offerEncodeMemory_read {mem : ByteArray} {callbackPtr output : UInt256} (offer : OfferData)
    (hc : MemoryByteString mem callbackPtr offer.callbackData)
    (hpad : paddedSize offer.callbackData.size < 2^64)
    (hbelow : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ output.toNat)
    (hout : output.toNat + offerEncodedSize offer + 64 < UInt256.size) :
    (offerEncodeMemory mem callbackPtr output offer).readWithPadding output.toNat
      (offerEncodedSize offer) = offerEncodedBytes offer := by
  obtain ⟨hw, hb, _, _⟩ := offerEncodeMemory_spec offer hc hpad hbelow hout
  exact offerEncodedRegions_read offer hw hb hout

end Benchmarks.Midnight
