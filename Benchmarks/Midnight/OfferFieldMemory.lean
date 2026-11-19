import Benchmarks.Midnight.OfferFirstFields
import Benchmarks.Midnight.OfferLastFields
import Benchmarks.Midnight.OfferHeapMemory

/-! The fixed field writes assemble the typed offer while preserving its dynamic children. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def offerSuffixMemory (mem bytes : ByteArray) (base : Nat) (callbackPtr : UInt256) : ByteArray :=
  offerLastMemory (offerTailPrefixMemory mem bytes base callbackPtr) bytes base

theorem offerSuffixMemory_words {mem bytes data : ByteArray} {base : Nat}
    {market : MarketData} {marketPtr callbackPtr : UInt256}
    (hfirst : MemoryWords mem 832 (offerFirstWords bytes base marketPtr))
    (hcanon : OfferData.canonicalAt bytes base) :
    MemoryWords (offerSuffixMemory mem bytes base callbackPtr) 832
      ((OfferData.at bytes base market data).words marketPtr callbackPtr) := by
  have ht := hfirst.append_writeWordArray (offerTailPrefixWords bytes base callbackPtr)
    (by change 832 + 32 * (8 + 5) < 2^256; decide)
  have hl := ht.append_writeWordArray (offerLastWords bytes base)
    (by change 832 + 32 * (8 + 5 + 2) < 2^256; decide)
  have hm := addressWord_eq_ofNat_address hcanon.2.1
  have hc := addressWord_eq_ofNat_address hcanon.2.2.1
  have hr := addressWord_eq_ofNat_address hcanon.2.2.2.1
  have hrat := addressWord_eq_ofNat_address hcanon.2.2.2.2.1
  change UInt256.ofNat (AccountAddress.ofNat (calldataWord bytes (base + 64)).toNat).val = _ at hm
  change UInt256.ofNat (AccountAddress.ofNat (calldataWord bytes (base + 224)).toNat).val = _ at hc
  change UInt256.ofNat (AccountAddress.ofNat (calldataWord bytes (base + 288)).toNat).val = _ at hr
  change UInt256.ofNat (AccountAddress.ofNat (calldataWord bytes (base + 320)).toNat).val = _ at hrat
  simpa only [offerSuffixMemory, offerLastMemory, offerTailPrefixMemory,
    OfferData.words, OfferData.at, offerFirstWords, offerTailPrefixWords, offerLastWords,
    List.length_append, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceMul,
    List.cons_append, List.nil_append, hm, hc, hr, hrat] using hl

theorem offerSuffixMemory_market {mem bytes : ByteArray} {base : Nat}
    {marketPtr arrayPtr callbackPtr : UInt256} {market : MarketData}
    (hmarket : MarketStored mem marketPtr arrayPtr callbackPtr market)
    (hlo : 1312 ≤ marketPtr.toNat) :
    MarketStored (offerSuffixMemory mem bytes base callbackPtr)
      marketPtr arrayPtr callbackPtr market := by
  apply MarketStored.writeWords_below
    (hmarket.writeWords_below (offerTailPrefixWords bytes base callbackPtr) (by
      change 1088 + 32 * 5 ≤ marketPtr.toNat; omega))
  change 1248 + 32 * 2 ≤ marketPtr.toNat
  omega

theorem offerSuffixMemory_callback {mem bytes data : ByteArray} {base : Nat}
    {callbackPtr : UInt256} (hcallback : MemoryByteString mem callbackPtr data)
    (hlo : 1312 ≤ callbackPtr.toNat) (hpad : paddedSize data.size < 2^64) :
    MemoryByteString (offerSuffixMemory mem bytes base callbackPtr) callbackPtr data := by
  exact MemoryByteString.writeWords_below (off := 1248)
    (hcallback.writeWords_below (off := 1088) (offerTailPrefixWords bytes base callbackPtr) (by
      change 1088 + 32 * 5 ≤ callbackPtr.toNat; omega) hpad)
    (offerLastWords bytes base) (by change 1248 + 32 * 2 ≤ callbackPtr.toNat; omega) hpad

theorem offerSuffixMemory_low {mem bytes : ByteArray} {base start : Nat}
    {callbackPtr : UInt256} {words : List UInt256}
    (hwords : MemoryWords mem start words) (hbelow : start + 32 * words.length ≤ 1088) :
    MemoryWords (offerSuffixMemory mem bytes base callbackPtr) start words :=
  (hwords.writeWords (off := 1088)
    (offerTailPrefixWords bytes base callbackPtr) (Or.inl hbelow)).writeWords (off := 1248)
    (offerLastWords bytes base) (Or.inl (by omega))

theorem offerSuffixMemory_load {mem bytes : ByteArray} {base : Nat}
    {callbackPtr read : UInt256} (hin : read.toNat + 32 ≤ mem.size)
    (hbelow : read.toNat + 32 ≤ 1088) :
    memLoad read (offerSuffixMemory mem bytes base callbackPtr) = memLoad read mem := by
  unfold offerSuffixMemory offerLastMemory offerTailPrefixMemory
  rw [memLoad_writeWordArray_below _ 1248 read _
      (hin.trans (writeWordArray_size_ge _ 1088 _)) (by omega),
    memLoad_writeWordArray_below mem 1088 read _ hin hbelow]

theorem offerSuffixMemory_size (mem bytes : ByteArray) (base : Nat) (callbackPtr : UInt256) :
    mem.size ≤ (offerSuffixMemory mem bytes base callbackPtr).size :=
  (writeWordArray_size_ge mem 1088 (offerTailPrefixWords bytes base callbackPtr)).trans
    (writeWordArray_size_ge _ 1248 (offerLastWords bytes base))

end Benchmarks.Midnight
