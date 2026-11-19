import Benchmarks.Midnight.OfferRestDecode

/-! A typed offer decoder with every ABI rejection condition retained. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def decodeOfferData (bytes : ByteArray) (start : Nat) : Option OfferData := do
  if ¬ (start + 480 ≤ bytes.size ∧ OfferData.canonicalAt bytes start) then none else
    let relative := (calldataWord bytes start).toNat
    if solcMaxU64 < relative then none else
      let market ← decodeMarketData bytes (start + relative)
      let data ← decodeRelativeBytes bytes start 256
      pure (OfferData.at bytes start market data)

theorem solcOfferValue_shape (bytes : ByteArray) (start : Nat) :
    decodeValue? Model.offerABI bytes.toList start {} =
      (if solcSLT (solcSub bytes.toList.length start) 480 then none else do
        let values ← decodeFields? (Model.marketABI :: offerRestTypes)
          bytes.toList start 0 [{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}] true
        pure (.tuple values)) := by
  have hhead : abiTupleHeadSize? (Model.marketABI :: offerRestTypes) = some 480 := by
    have hm : isDynamicABIType Model.marketABI = true := by decide +kernel
    simp [offerRestTypes, abiTupleHeadSize?, hm, Model.u256, Model.u128, Model.addr,
      Model.b32, isDynamicABIType, staticABIEncodedSize?]
  have hd : isDynamicABIType Model.offerABI = true := by decide +kernel
  change decodeValue? (.tuple (Model.marketABI :: offerRestTypes)) bytes.toList start {} = _
  rw [decodeValue?]
  simp only [hhead, bind, Option.bind, show isMemory ({} : CalldataPlan) = true from rfl,
    Bool.not_false, Bool.true_or, Bool.true_and, hd, Bool.not_true,
    Bool.false_eq_true, if_false]
  rfl

theorem solcOfferValue_eq {bytes : ByteArray} {start : Nat}
    (hsize : bytes.size < 2^255) (hstart : start < 2^126) :
    decodeValue? Model.offerABI bytes.toList start {} =
      (decodeOfferData bytes start).map OfferData.value := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]
    rfl
  have hmod : bytes.size < UInt256.size := by change bytes.size < 2^256; omega
  rw [solcOfferValue_shape, hl, solcSLT_sub_small hsize (by omega) (by norm_num)]
  by_cases hlen : start + 480 ≤ bytes.size
  · simp only [show ¬ bytes.size < start + 480 from by omega, decide_false,
      Bool.false_eq_true, if_false]
    rw [solcDecodeFields_dynamic Model.marketABI (by decide +kernel) rfl (by omega) hmod
      (by change start + 2^64 < 2^256; omega)]
    simp only [List.tail_cons, Nat.add_zero]
    by_cases ho : solcMaxU64 < (calldataWord bytes start).toNat
    · simp [decodeOfferData, hlen, ho, bind, Option.bind]
    · have hs : start + (calldataWord bytes start).toNat < 2^127 := by
        change ¬ (2^64 - 1 < _) at ho
        omega
      simp only [ho, if_false, solcMarketValue_eq hsize hs,
        solcDecodeOfferRest (by omega) hlen hmod]
      by_cases hc : OfferData.canonicalAt bytes start
      · simp only [decodeOfferData, hlen, hc, and_self, not_true_eq_false, if_false,
          if_true, ho]
        cases decodeMarketData bytes (start + (calldataWord bytes start).toNat) <;>
          cases decodeRelativeBytes bytes start 256 <;> rfl
      · simp only [decodeOfferData, hc, and_false, not_false_eq_true, if_true, if_false,
          Option.map_none]
        cases decodeMarketData bytes (start + (calldataWord bytes start).toNat) <;> rfl
  · simp [decodeOfferData, hlen, show bytes.size < start + 480 from by omega]

end Benchmarks.Midnight
