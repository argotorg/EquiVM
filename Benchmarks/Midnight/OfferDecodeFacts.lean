import Benchmarks.Midnight.OfferCalldataHead
import Benchmarks.Midnight.CalldataHeadCheck

/-! Failure and field facts for the materialized offer decoder. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem decodeOfferData_none_noncanon {bytes : ByteArray} {base : Nat}
    (h : ¬ OfferData.canonicalAt bytes base) : decodeOfferData bytes base = none := by
  simp [decodeOfferData, h]

theorem decodeOfferData_none_callback {bytes : ByteArray} {base : Nat}
    (h : decodeRelativeBytes bytes base 256 = none) : decodeOfferData bytes base = none := by
  unfold decodeOfferData
  split
  · rfl
  dsimp only
  split
  · rfl
  rw [h]
  cases decodeMarketData bytes (base + (calldataWord bytes base).toNat) <;> rfl

theorem decodeOfferData_none_callbackOffset {bytes : ByteArray} {base : Nat}
    (h : ¬ (calldataWord bytes (base + 256)).toNat < 2^64) :
    decodeOfferData bytes base = none := by
  apply decodeOfferData_none_callback
  simp only [decodeRelativeBytes, h, if_false]

theorem decodeOfferData_none_marketOffset {bytes : ByteArray} {base : Nat}
    (h : ¬ (calldataWord bytes base).toNat < 2^64) :
    decodeOfferData bytes base = none := by
  have hc : solcMaxU64 < (calldataWord bytes base).toNat := by
    change 2^64 - 1 < _
    omega
  simp [decodeOfferData, hc]

theorem decodeOfferData_success {bytes : ByteArray} {base : Nat} {offer : OfferData}
    (h : decodeOfferData bytes base = some offer) :
    base + 480 ≤ bytes.size ∧ OfferData.canonicalAt bytes base ∧
      (calldataWord bytes base).toNat < 2^64 ∧
      ∃ market data,
        decodeMarketData bytes (base + (calldataWord bytes base).toNat) = some market ∧
        decodeRelativeBytes bytes base 256 = some data ∧
        offer = OfferData.at bytes base market data := by
  unfold decodeOfferData at h
  split at h
  · cases h
  rename_i hv
  have hv' : base + 480 ≤ bytes.size ∧ OfferData.canonicalAt bytes base := by tauto
  dsimp only at h
  split at h
  · cases h
  rename_i ho
  have ho' : (calldataWord bytes base).toNat < 2^64 := by
    change ¬ (2^64 - 1 < _) at ho
    omega
  cases hm : decodeMarketData bytes (base + (calldataWord bytes base).toNat) with
  | none => simp only [hm, bind, Option.bind] at h; cases h
  | some market =>
    cases hd : decodeRelativeBytes bytes base 256 with
    | none => simp only [hm, hd, bind, Option.bind] at h; cases h
    | some data =>
      simp only [hm, hd, bind, Option.bind, pure, Option.some.injEq] at h
      exact ⟨hv'.1, hv'.2, ho', market, data, rfl, rfl, h.symm⟩

theorem decodeCalldataOffer_success {bytes : ByteArray} {slot : Nat} {offer : OfferData}
    (h : decodeCalldataOffer bytes slot = some offer) :
    (calldataWord bytes slot).toNat < 2^64 ∧ bytes.size < 2^255 ∧
      decodeOfferData bytes (4 + (calldataWord bytes slot).toNat) = some offer := by
  unfold decodeCalldataOffer at h
  dsimp only at h
  split at h
  · cases h
  rename_i hv
  have ho : (calldataWord bytes slot).toNat < 2^64 := by
    change ¬ (2^64 - 1 < _ ∨ 2^255 ≤ _) at hv
    omega
  exact ⟨ho, by omega, h⟩

theorem decodeCalldataOffer_headerCheck {bytes : ByteArray} {offer : OfferData}
    (h : decodeCalldataOffer bytes 4 = some offer) :
    UInt256.slt (UInt256.sub (UInt256.ofNat bytes.size) (calldataWord bytes 4) +
      UInt256.lnot (UInt256.ofNat 3)) (UInt256.ofNat 480) = UInt256.ofNat 0 := by
  obtain ⟨ho, hs, hd⟩ := decodeCalldataOffer_success h
  have hb := (decodeOfferData_success hd).1
  have hh := calldataArgumentHead_toNat ho
  change (UInt256.ofNat 4 + calldataWord bytes 4).toNat = _ at hh
  change UInt256.slt (UInt256.sub (UInt256.ofNat bytes.size) (calldataWord bytes 4) +
    UInt256.lnot ⟨3⟩) (UInt256.ofNat 480) = UInt256.ofNat 0
  rw [u256_add_comm, lnot3_add_sub_word]
  have hc := signedDecodeCheck (finish := UInt256.ofNat bytes.size)
    (start := UInt256.ofNat 4 + calldataWord bytes 4) (need := 480)
    (by rw [UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]; exact hs)
    (by rw [hh]; omega) (by decide)
  rw [UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega), hh,
    decide_eq_false (by omega)] at hc
  exact hc

end Benchmarks.Midnight
