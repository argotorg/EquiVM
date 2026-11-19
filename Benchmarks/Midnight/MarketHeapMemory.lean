import Benchmarks.Midnight.ToMarketHeapMemory
import Benchmarks.Midnight.MarketCalldataLastFields

/-! The complete market record and its collateral pointers in the runtime heap. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure MarketStored (mem : ByteArray) (ptr arrayPtr root : UInt256) (m : MarketData) : Prop where
  words : MemoryWords mem ptr.toNat (m.words arrayPtr)
  header : MemoryWords mem arrayPtr.toNat [UInt256.ofNat m.collaterals.length]
  collaterals : CollateralListStored mem (arrayPtr + UInt256.ofNat 32) root.toNat m.collaterals
  lower : 96 ≤ ptr.toNat
  array : ptr.toNat + 256 ≤ arrayPtr.toNat
  extent : arrayPtr.toNat + 32 ≤ root.toNat
  bound : root.toNat < 2^64

theorem marketLastMemory_stored {mem bytes : ByteArray} {start : Nat}
    {ptr arrayPtr root : UInt256} {cs : List CollateralData}
    (hfirst : MemoryWords mem ptr.toNat (marketFirstWords bytes start))
    (hheader : MemoryWords mem arrayPtr.toNat [UInt256.ofNat cs.length])
    (hc : CollateralListStored mem (arrayPtr + UInt256.ofNat 32) root.toNat cs)
    (hlo : 96 ≤ ptr.toNat) (harray : ptr.toNat + 256 ≤ arrayPtr.toNat)
    (hextent : arrayPtr.toNat + 32 ≤ root.toNat) (hroot : root.toNat < 2^64)
    (hcanon : MarketData.canonicalAt bytes start) :
    MarketStored (marketLastMemory mem ptr arrayPtr bytes start) ptr arrayPtr root
      (MarketData.at bytes start cs) := by
  have ha32 : (arrayPtr + UInt256.ofNat 32).toNat = arrayPtr.toNat + 32 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  refine ⟨?_, ?_, ?_, hlo, harray, hextent, hroot⟩
  · have hh := hfirst.append_writeWordArray (marketLastWords bytes start arrayPtr) (by
      change ptr.toNat + 32 * 8 < 2^256
      omega)
    rcases hcanon with ⟨hm, hl, he, hliq⟩
    have hmid : UInt256.ofNat (AccountAddress.ofNat
        (calldataWord bytes (start + 32)).toNat).val = calldataWord bytes (start + 32) :=
      addressWord_eq_ofNat_address hm
    have hloan : UInt256.ofNat (AccountAddress.ofNat
        (calldataWord bytes (start + 64)).toNat).val = calldataWord bytes (start + 64) :=
      addressWord_eq_ofNat_address hl
    have henter : UInt256.ofNat (AccountAddress.ofNat
        (calldataWord bytes (start + 192)).toNat).val = calldataWord bytes (start + 192) :=
      addressWord_eq_ofNat_address he
    have hliquid : UInt256.ofNat (AccountAddress.ofNat
        (calldataWord bytes (start + 224)).toNat).val = calldataWord bytes (start + 224) :=
      addressWord_eq_ofNat_address hliq
    simpa only [MarketData.at, MarketData.words, marketLastMemory,
      marketFirstWords, marketLastWords, marketTailWords, List.length_cons, List.length_nil,
      Nat.reduceAdd, Nat.reduceMul, List.cons_append, List.nil_append,
      hmid, hloan, henter, hliquid] using hh
  · exact hheader.writeWords (marketLastWords bytes start arrayPtr) (Or.inr (by
      change ptr.toNat + 96 + 32 * 5 ≤ arrayPtr.toNat
      omega))
  · exact hc.writeWords_below (marketLastWords bytes start arrayPtr) hroot (by
      change ptr.toNat + 96 + 32 * 5 ≤ (arrayPtr + UInt256.ofNat 32).toNat
      rw [ha32]
      omega)

theorem marketLastMemory_free {mem bytes : ByteArray} {start : Nat}
    {ptr arrayPtr root : UInt256}
    (hfree : memLoad (UInt256.ofNat 64) mem = root)
    (hin : 96 ≤ mem.size) (hlo : 96 ≤ ptr.toNat) :
    memLoad (UInt256.ofNat 64) (marketLastMemory mem ptr arrayPtr bytes start) = root := by
  rw [marketLastMemory, memLoad_writeWordArray_preserved _ _ (UInt256.ofNat 64) _ hin
    (Or.inl (by change 64 + 32 ≤ ptr.toNat + 96; omega)), hfree]

end Benchmarks.Midnight
