import Benchmarks.Midnight.OfferCalldataValue

/-! The dynamic offer argument and its signed calldata-length rejection. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def decodeCalldataOffer (bytes : ByteArray) (head : Nat) : Option OfferData :=
  let relative := (calldataWord bytes head).toNat
  if solcMaxU64 < relative ∨ 2^255 ≤ bytes.size then none
  else decodeOfferData bytes (4 + relative)

theorem solcOfferValue_huge {bytes : ByteArray} {start : Nat}
    (hhigh : 2^255 ≤ bytes.size) (hsize : bytes.size < UInt256.size)
    (hstart : start < 2^126) :
    decodeValue? Model.offerABI bytes.toList start {} = none := by
  rw [solcOfferValue_shape]
  split
  · rfl
  · rw [solcDecodeFields_dynamic Model.marketABI (by decide +kernel) rfl
      (by omega) hsize (by change start + 2^64 < 2^256; omega)]
    simp only [Nat.add_zero]
    by_cases ho : solcMaxU64 < (calldataWord bytes start).toNat
    · simp only [ho, if_true, bind, Option.bind]
    · rw [if_neg ho, solcMarketValue_huge hhigh hsize (by
        change ¬ (2^64 - 1 < _) at ho
        omega)]
      rfl

theorem solcDecodeFields_offer {types : List ABIType} {bytes : ByteArray}
    {cursor : Nat} {plans : List CalldataPlan}
    (hplan : plans.headD {} = {}) (hbound : 4 + cursor + 32 ≤ bytes.size)
    (hsize : bytes.size < UInt256.size) :
    decodeFields? (Model.offerABI :: types) bytes.toList 4 cursor plans true = (do
      let offer ← decodeCalldataOffer bytes (4 + cursor)
      let rest ← decodeFields? types bytes.toList 4 (cursor + 32) plans.tail true
      pure (offer.value :: rest)) := by
  rw [solcDecodeFields_dynamic Model.offerABI (by decide +kernel) hplan hbound hsize
    (by decide +kernel)]
  unfold decodeCalldataOffer
  by_cases ho : solcMaxU64 < (calldataWord bytes (4 + cursor)).toNat
  · simp only [ho, true_or, if_true, bind, Option.bind]
  · have hs : 4 + (calldataWord bytes (4 + cursor)).toNat < 2^126 := by
      change ¬ (2^64 - 1 < _) at ho
      omega
    simp only [ho, false_or, if_false]
    by_cases hh : 2^255 ≤ bytes.size
    · rw [solcOfferValue_huge hh hsize hs]
      simp only [hh, if_true, bind, Option.bind]
    · rw [solcOfferValue_eq (by omega) hs]
      simp only [hh, if_false]
      cases decodeOfferData bytes (4 + (calldataWord bytes (4 + cursor)).toNat) <;> rfl

end Benchmarks.Midnight
