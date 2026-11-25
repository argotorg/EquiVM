import Benchmarks.Midnight.OfferFieldMemory
import Benchmarks.Midnight.BytesCalldataMemory

/-! Assemble the decoded offer's record, market, callback buffer, and preserved lower words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def offerCallbackMemory (mem bytes : ByteArray) (base : Nat) (marketPtr callbackPtr : UInt256) :
    ByteArray :=
  bytesCalldataMemory (offerFirstMemory mem bytes base marketPtr) bytes callbackPtr
    (base + (calldataWord bytes (base + 256)).toNat)

def offerDecodedMemory (mem bytes : ByteArray) (base : Nat) (marketPtr callbackPtr : UInt256) :
    ByteArray :=
  offerSuffixMemory (offerCallbackMemory mem bytes base marketPtr callbackPtr) bytes base callbackPtr

theorem offerDecodedMemory_stored {mem bytes data : ByteArray} {base : Nat}
    {market : MarketData} {marketPtr arrayPtr callbackPtr : UInt256}
    (hmarket : MarketStored mem marketPtr arrayPtr callbackPtr market)
    (hlo : 1312 ≤ marketPtr.toNat) (hcanon : OfferData.canonicalAt bytes base)
    (hd : decodeBytesAt bytes (base + (calldataWord bytes (base + 256)).toNat) = some data)
    (hfit : callbackPtr.toNat + returnDataAllocation data.size < 2^64) :
    OfferStored (offerDecodedMemory mem bytes base marketPtr callbackPtr)
      ⟨832⟩ marketPtr arrayPtr callbackPtr (returnDataPtr callbackPtr data.size)
      (OfferData.at bytes base market data) := by
  have hcb : 1600 ≤ callbackPtr.toNat := by
    have ha := hmarket.array
    have he := hmarket.extent
    omega
  let m1 := offerFirstMemory mem bytes base marketPtr
  have hw1 : MemoryWords m1 832 (offerFirstWords bytes base marketPtr) :=
    MemoryWords.of_writeWordArray mem 832 _ (by change 832 + 32 * 8 < 2^256; decide)
      (by simp [offerFirstWords])
  have hm1 : MarketStored m1 marketPtr arrayPtr callbackPtr market :=
    hmarket.writeWords_below (off := 832) (offerFirstWords bytes base marketPtr)
      (by change 832 + 32 * 8 ≤ marketPtr.toNat; omega)
  have hp := bytesCalldataMemory_prefix (mem := m1) (ptr := callbackPtr) hd
  have hw2 : MemoryWords (offerCallbackMemory mem bytes base marketPtr callbackPtr) 832
      (offerFirstWords bytes base marketPtr) := by
    apply hw1.preserve hp.size
    intro read hrlo hrhi
    exact hp.load read (by omega) (by
      change read.toNat + 32 ≤ 832 + 32 * 8 at hrhi; omega) (hrhi.trans hw1.size)
  have hm2 : MarketStored (offerCallbackMemory mem bytes base marketPtr callbackPtr)
      marketPtr arrayPtr callbackPtr market := hm1.preserve hp
  have hd2 : MemoryByteString (offerCallbackMemory mem bytes base marketPtr callbackPtr)
      callbackPtr data := bytesCalldataMemory_stored hd (by omega) hfit
  have hpad : paddedSize data.size < 2^64 := by
    rw [returnDataAllocation_eq] at hfit
    omega
  refine ⟨offerSuffixMemory_words hw2 hcanon,
    offerSuffixMemory_market hm2 hlo, offerSuffixMemory_callback hd2 (by omega) hpad,
    by decide, hlo, ?_, ?_⟩
  · change callbackPtr.toNat + 32 + paddedSize data.size ≤ _
    rw [returnDataPtr_toNat hfit, returnDataAllocation_eq]
    omega
  · rw [returnDataPtr_toNat hfit]
    exact hfit

theorem offerDecodedMemory_free {mem bytes data : ByteArray} {base : Nat}
    {marketPtr callbackPtr : UInt256}
    (hlo : 96 ≤ callbackPtr.toNat)
    (hd : decodeBytesAt bytes (base + (calldataWord bytes (base + 256)).toNat) = some data) :
    memLoad (UInt256.ofNat 64) (offerDecodedMemory mem bytes base marketPtr callbackPtr) =
      returnDataPtr callbackPtr data.size := by
  have hs := bytesCalldataMemory_size (mem := offerFirstMemory mem bytes base marketPtr)
    (ptr := callbackPtr) hd
  change callbackPtr.toNat + returnDataAllocation data.size ≤
    (offerCallbackMemory mem bytes base marketPtr callbackPtr).size at hs
  unfold offerDecodedMemory
  rw [offerSuffixMemory_load (read := UInt256.ofNat 64) (by
      change 64 + 32 ≤ _
      omega)
      (by decide)]
  exact bytesCalldataMemory_free hd hlo

theorem offerDecodedMemory_size {mem bytes data : ByteArray} {base : Nat}
    {marketPtr callbackPtr : UInt256}
    (hd : decodeBytesAt bytes (base + (calldataWord bytes (base + 256)).toNat) = some data)
    (hfit : callbackPtr.toNat + returnDataAllocation data.size < 2^64) :
    (returnDataPtr callbackPtr data.size).toNat ≤
      (offerDecodedMemory mem bytes base marketPtr callbackPtr).size := by
  rw [returnDataPtr_toNat hfit]
  exact (bytesCalldataMemory_size (mem := offerFirstMemory mem bytes base marketPtr) hd).trans
    (offerSuffixMemory_size _ _ _ _)

theorem offerDecodedMemory_low {mem bytes data : ByteArray} {base start : Nat}
    {marketPtr callbackPtr : UInt256} {words : List UInt256}
    (hwords : MemoryWords mem start words) (hstart : 96 ≤ start)
    (hbelow : start + 32 * words.length ≤ 832) (hcb : 832 ≤ callbackPtr.toNat)
    (hd : decodeBytesAt bytes (base + (calldataWord bytes (base + 256)).toNat) = some data) :
    MemoryWords (offerDecodedMemory mem bytes base marketPtr callbackPtr) start words := by
  have hw1 := hwords.writeWords (off := 832) (offerFirstWords bytes base marketPtr) (Or.inl hbelow)
  have hp := bytesCalldataMemory_prefix (mem := offerFirstMemory mem bytes base marketPtr)
    (ptr := callbackPtr) hd
  apply offerSuffixMemory_low _ (by omega)
  apply hw1.preserve hp.size
  intro read hrlo hrhi
  exact hp.load read (by omega) (by omega) (hrhi.trans hw1.size)

end Benchmarks.Midnight
