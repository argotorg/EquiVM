import Benchmarks.Midnight.OfferData
import Benchmarks.Midnight.MemoryByteString
import Benchmarks.Midnight.LiquidatePositionMemory

/-! The complete in-memory offer, its market, and its callback bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem MarketStored.writeWords_below {mem : ByteArray} {ptr arrayPtr root : UInt256}
    {m : MarketData} {off : Nat} (h : MarketStored mem ptr arrayPtr root m)
    (words : List UInt256) (hbelow : off + 32 * words.length ≤ ptr.toNat) :
    MarketStored (writeWordArray mem off words) ptr arrayPtr root m := by
  induction words generalizing mem off with
  | nil => exact h
  | cons word rest ih =>
    simp only [List.length_cons] at hbelow
    exact ih (h.writeWord_below word (by omega)) (by omega)

structure OfferStored (mem : ByteArray) (ptr marketPtr arrayPtr callbackPtr root : UInt256)
    (offer : OfferData) : Prop where
  words : MemoryWords mem ptr.toNat (offer.words marketPtr callbackPtr)
  market : MarketStored mem marketPtr arrayPtr callbackPtr offer.market
  callback : MemoryByteString mem callbackPtr offer.callbackData
  lower : 96 ≤ ptr.toNat
  layout : ptr.toNat + 480 ≤ marketPtr.toNat
  extent : callbackPtr.toNat + 32 + paddedSize offer.callbackData.size ≤ root.toNat
  bound : root.toNat < 2^64

theorem OfferStored.preserve {before after : ByteArray}
    {ptr marketPtr arrayPtr callbackPtr root : UInt256} {offer : OfferData}
    (h : OfferStored before ptr marketPtr arrayPtr callbackPtr root offer)
    (hp : MemoryPrefix before after root.toNat) :
    OfferStored after ptr marketPtr arrayPtr callbackPtr root offer := by
  refine ⟨?_, h.market.preserve (hp.mono (by have := h.extent; omega)),
    h.callback.preserve hp h.extent, h.lower, h.layout, h.extent, h.bound⟩
  apply h.words.preserve hp.size
  intro read hlo hhi
  apply hp.load read (h.lower.trans hlo) _ (hhi.trans h.words.size)
  simp only [OfferData.words, List.length_cons, List.length_nil, Nat.reduceAdd] at hhi
  have hl := h.layout
  have ha := h.market.array
  have he := h.market.extent
  have hb := h.extent
  omega

theorem OfferStored.writeWord_below {mem : ByteArray}
    {ptr marketPtr arrayPtr callbackPtr root : UInt256} {offer : OfferData} {off : Nat}
    (h : OfferStored mem ptr marketPtr arrayPtr callbackPtr root offer) (word : UInt256)
    (hbelow : off + 32 ≤ ptr.toNat) :
    OfferStored (writeWord mem off word) ptr marketPtr arrayPtr callbackPtr root offer := by
  have hl := h.layout
  have ha := h.market.array
  have he := h.market.extent
  have hc := h.extent
  have hb := h.bound
  exact ⟨h.words.writeWord word (Or.inr hbelow),
    h.market.writeWord_below word (by omega),
    h.callback.writeWord_below word (by omega) (by omega),
    h.lower, h.layout, h.extent, h.bound⟩

end Benchmarks.Midnight
