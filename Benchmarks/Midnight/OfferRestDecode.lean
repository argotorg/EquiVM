import Benchmarks.Midnight.OfferTailDecode
import Benchmarks.Midnight.RelativeBytesDecode
import Benchmarks.Midnight.MarketEntryDecode

/-! The offer fields following its nested market, including callback bytes. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def offerRestTypes : List ABIType :=
  [.elem .bool, Model.addr, Model.u256, Model.u256, Model.u256, Model.b32, Model.addr,
    .bytes, Model.addr, Model.addr, .elem .bool, Model.u128, Model.u128, Model.u256]

def offerRestValues (bytes : ByteArray) (base : Nat) (data : ByteArray) : List Value :=
  [wordToElem .bool (calldataWord bytes (base + 32)),
    .address (AccountAddress.ofNat (calldataWord bytes (base + 64)).toNat),
    .int (calldataWord bytes (base + 96)).toNat,
    .int (calldataWord bytes (base + 128)).toNat,
    .int (calldataWord bytes (base + 160)).toNat,
    wordBytes32Value (calldataWord bytes (base + 192)),
    .address (AccountAddress.ofNat (calldataWord bytes (base + 224)).toNat),
    .bytes data] ++ offerTailValues bytes base

theorem solcDecodeOfferRest {bytes : ByteArray} {base : Nat}
    (hbase : base < 2^127) (hlen : base + 480 ≤ bytes.size)
    (hsize : bytes.size < UInt256.size) :
    decodeFields? offerRestTypes bytes.toList base 32
      [{}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}, {}] true =
      if OfferData.canonicalAt bytes base then (do
        let data ← decodeRelativeBytes bytes base 256
        pure (offerRestValues bytes base data)) else none := by
  unfold offerRestTypes
  rw [solcDecodeFields_word (.elem .bool) rfl rfl (by omega) hsize, decodeABIWord_bool]
  by_cases hb : calldataWord bytes (base + 32) = ⟨0⟩ ∨
      calldataWord bytes (base + 32) = ⟨1⟩
  · simp only [hb, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
    rw [solcDecodeFields_word Model.addr rfl rfl (by omega) hsize, decodeABIWord_address]
    by_cases hm : (calldataWord bytes (base + 64)).toNat < EVM.addressModulus
    · simp only [hm, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
      rw [solcDecodeFields_word Model.u256 rfl rfl (by omega) hsize, decodeABIWord_u256]
      simp only [bind, Option.bind, Nat.reduceAdd, List.tail_cons]
      rw [solcDecodeFields_word Model.u256 rfl rfl (by omega) hsize, decodeABIWord_u256]
      simp only [bind, Option.bind, Nat.reduceAdd, List.tail_cons]
      rw [solcDecodeFields_word Model.u256 rfl rfl (by omega) hsize, decodeABIWord_u256]
      simp only [bind, Option.bind, Nat.reduceAdd, List.tail_cons]
      rw [solcDecodeFields_bytes32 rfl (by omega) hsize]
      simp only [Nat.reduceAdd, List.tail_cons]
      rw [solcDecodeFields_word Model.addr rfl rfl (by omega) hsize, decodeABIWord_address]
      by_cases hc : (calldataWord bytes (base + 224)).toNat < EVM.addressModulus
      · simp only [hc, if_true, bind, Option.bind, Nat.reduceAdd, List.tail_cons]
        rw [solcDecodeFields_relativeBytes rfl hbase (by omega) hsize]
        simp only [Nat.reduceAdd, List.tail_cons]
        rw [solcDecodeOfferTail hlen hsize]
        cases hd : decodeRelativeBytes bytes base 256 <;>
          by_cases ht : OfferData.tailCanonicalAt bytes base <;>
          simp only [OfferData.canonicalAt, hb, hm, hc, ht, and_self, and_true, and_false,
            if_true, if_false, bind, Option.bind, pure, offerRestValues, List.cons_append,
            List.nil_append]
        rfl
      · simp only [OfferData.canonicalAt, hc, false_and, and_false, if_false,
          bind, Option.bind]
    · simp only [OfferData.canonicalAt, hm, false_and, and_false, if_false,
        bind, Option.bind]
  · simp only [OfferData.canonicalAt, hb, false_and, if_false, bind, Option.bind]

end Benchmarks.Midnight
