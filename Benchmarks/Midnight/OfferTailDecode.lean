import Benchmarks.Midnight.OfferData
import Benchmarks.Midnight.MarketCalldataFields

/-! The six final scalar fields of an offer, including both uint128 caps. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

theorem decodeABIWord_u128 (word : UInt256) :
    decodeABIWord? Model.u128 word =
      if word.toNat < 2^128 then some (.int word.toNat) else none := rfl

def offerTailValues (bytes : ByteArray) (base : Nat) : List Value :=
  [.address (AccountAddress.ofNat (calldataWord bytes (base + 288)).toNat),
    .address (AccountAddress.ofNat (calldataWord bytes (base + 320)).toNat),
    wordToElem .bool (calldataWord bytes (base + 352)),
    .int (calldataWord bytes (base + 384)).toNat,
    .int (calldataWord bytes (base + 416)).toNat,
    .int (calldataWord bytes (base + 448)).toNat]

theorem solcDecodeOfferTail {bytes : ByteArray} {base : Nat}
    (hlen : base + 480 ≤ bytes.size) (hsize : bytes.size < UInt256.size) :
    decodeFields? [Model.addr, Model.addr, .elem .bool, Model.u128, Model.u128, Model.u256]
      bytes.toList base 288 [{}, {}, {}, {}, {}, {}] true =
      if OfferData.tailCanonicalAt bytes base then some (offerTailValues bytes base)
      else none := by
  rw [solcDecodeFields_word Model.addr rfl rfl (by omega) hsize, decodeABIWord_address]
  by_cases hr : (calldataWord bytes (base + 288)).toNat < EVM.addressModulus
  · simp only [hr, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
    rw [solcDecodeFields_word Model.addr rfl rfl (by omega) hsize, decodeABIWord_address]
    by_cases ha : (calldataWord bytes (base + 320)).toNat < EVM.addressModulus
    · simp only [ha, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
      rw [solcDecodeFields_word (.elem .bool) rfl rfl (by omega) hsize, decodeABIWord_bool]
      by_cases hb : calldataWord bytes (base + 352) = ⟨0⟩ ∨
          calldataWord bytes (base + 352) = ⟨1⟩
      · simp only [hb, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
        rw [solcDecodeFields_word Model.u128 rfl rfl (by omega) hsize, decodeABIWord_u128]
        by_cases hu : (calldataWord bytes (base + 384)).toNat < 2^128
        · simp only [hu, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
          rw [solcDecodeFields_word Model.u128 rfl rfl (by omega) hsize, decodeABIWord_u128]
          by_cases hv : (calldataWord bytes (base + 416)).toNat < 2^128
          · simp only [hv, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
            rw [solcDecodeFields_word Model.u256 rfl rfl (by omega) hsize, decodeABIWord_u256]
            simp only [OfferData.tailCanonicalAt, hr, ha, hb, hu, hv, and_self, if_true,
              bind, Option.bind, decodeFields?, pure, offerTailValues, Nat.reduceAdd]
            rfl
          · simp only [OfferData.tailCanonicalAt, hv, and_false, if_false, bind, Option.bind]
        · simp only [OfferData.tailCanonicalAt, hu, false_and, and_false, if_false,
            bind, Option.bind]
      · simp only [OfferData.tailCanonicalAt, hb, false_and, and_false, if_false,
          bind, Option.bind]
    · simp only [OfferData.tailCanonicalAt, ha, false_and, and_false, if_false,
        bind, Option.bind]
  · simp only [OfferData.tailCanonicalAt, hr, false_and, if_false, bind, Option.bind]

end Benchmarks.Midnight
