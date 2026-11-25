import Benchmarks.Midnight.OfferDecodeFacts

/-! The boolean and uint128 bounds guaranteed by successful offer decoding. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

structure OfferCanonical (offer : OfferData) : Prop where
  buy : offer.buy = ⟨0⟩ ∨ offer.buy = ⟨1⟩
  reduceOnly : offer.reduceOnly = ⟨0⟩ ∨ offer.reduceOnly = ⟨1⟩
  maxUnits : offer.maxUnits.toNat < 2^128
  maxAssets : offer.maxAssets.toNat < 2^128

theorem decodeCalldataOffer_canonical {bytes : ByteArray} {slot : Nat} {offer : OfferData}
    (hd : decodeCalldataOffer bytes slot = some offer) : OfferCanonical offer := by
  obtain ⟨_, _, hd'⟩ := decodeCalldataOffer_success hd
  obtain ⟨_, hc, _, market, data, _, _, he⟩ := decodeOfferData_success hd'
  rw [he]
  exact ⟨hc.1, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2.1, hc.2.2.2.2.2.2.2⟩

end Benchmarks.Midnight
