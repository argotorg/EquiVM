import Solm.Benchmarks.Auction.UIntReturnDecoder
import Solm.Benchmarks.Auction.ErrorDecodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: convert a byte-array slice to the decoder's list representation.
theorem extract_toList (out : ByteArray) (start finish : Nat) :
    (out.extract start finish).toList = (out.toList.drop start).take (finish - start) := by
  simp only [byteArray_toList_eq, ByteArray.data_extract, Array.toList_extract,
    List.extract_eq_take_drop]

-- LIBRARY CANDIDATE: a complete word is unchanged by taking an enclosing byte-array slice.
theorem calldataWord_extract_zero {out : ByteArray} {start finish : Nat}
    (hs : start + 32 ≤ finish) (he : finish ≤ out.size) :
    calldataWord (out.extract start finish) 0 = calldataWord out start := by
  have hl : 32 ≤ (out.extract start finish).size := by
    rw [ByteArray.size_extract]
    omega
  have hw : bytesToWord (((out.extract start finish).toList.drop 0).take 32) =
      calldataWord (out.extract start finish) 0 :=
    decode_word_at_eq_any (out.extract start finish) 0 hl
  rw [← hw,
    extract_toList, List.drop_zero, List.take_take, Nat.min_eq_left (by omega),
    decode_word_at_eq_any out start (by omega)]

-- LIBRARY CANDIDATE: decode a uint256 from a bounded byte-array slice.
theorem decodeReturnUint_extract {out : ByteArray} {start finish : Nat}
    (hs : start + 32 ≤ finish) (he : finish ≤ out.size) (hb : finish - start < 2 ^ 255) :
    ABI.decodeReturnValue? (.elem (.int (.uint ⟨256, by decide⟩)))
      (out.extract start finish) = some (.int (Int.ofNat (calldataWord out start).toNat)) := by
  rw [decodeReturnUint_long (by rw [ByteArray.size_extract]; omega)
    (by rw [ByteArray.size_extract]; omega), calldataWord_extract_zero hs he]

-- LIBRARY CANDIDATE: dynamic string return decoding from its three successful reads.
theorem decodeReturnString_of_reads {out : ByteArray} {offset len : Nat} {payload : List UInt8}
    (hb : out.toList.length < 2 ^ 255)
    (ho : readNat? out.toList 0 = some offset)
    (hl : readNat? out.toList offset = some len)
    (hp : readBytes? out.toList (offset + 32) len = some payload)
    (ho64 : offset ≤ solcMaxU64) (hl64 : len ≤ solcMaxU64) :
    ABI.decodeReturnValue? .string out = some (.bytes ⟨payload.toArray⟩) := by
  unfold ABI.decodeReturnValue? ABI.decodeReturnValues?
  rw [if_neg (by simp only [List.isEmpty_cons]; omega)]
  have hh : abiTupleHeadSize? [.string] = some 32 := by native_decide
  simp only [hh, bind, Option.bind, decodeABIValues?, isDynamicABIType, ↓reduceIte,
    Nat.zero_add, ho, solcMaxLen, show ¬ solcMaxU64 < offset by omega,
    decodeABIValue?, hl, show ¬ solcMaxU64 < len by omega, hp]

theorem errorReturnString_ok {out : ByteArray} (hv : ErrorDataValid out)
    (hb : out.size < 2 ^ 255) :
    ∃ value, ABI.decodeReturnValue? .string (out.extract 4 out.size) = some value := by
  have ht : out.toList.length = out.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have hx : (out.extract 4 out.size).toList = out.toList.drop 4 := by
    rw [extract_toList, ← ht, ← List.length_drop, List.take_length]
  have ho := readNat_drop4_zero_eq_calldataWord (cd := out) (by have h := hv.1; omega)
  have hl := readNat_drop4_dynamic_eq_calldataWord (cd := out)
    (by change 4 + (errorOffset out).toNat + 32 ≤ out.size; have h := hv.2.1.2; omega)
  have hpay := hv.2.2.2
  simp only [errorLength, errorOffset] at hpay
  have hp := readBytes_drop4_string_payload (cd := out) (by
    simp only [List.length_take, List.length_drop, ht]
    omega)
  refine ⟨_, decodeReturnString_of_reads (offset := (errorOffset out).toNat)
    (len := (errorLength out).toNat)
    (payload := ((out.toList.drop 4).drop ((errorOffset out).toNat + 32)).take
      (errorLength out).toNat) ?_ ?_ ?_ ?_ hv.2.1.1 hv.2.2.1⟩
  · rw [hx, List.length_drop, ht]
    omega
  · simpa only [hx, errorOffset] using ho
  · simpa only [hx, errorLength, errorOffset] using hl
  · simpa only [hx, errorLength, errorOffset] using hp

end Auction
