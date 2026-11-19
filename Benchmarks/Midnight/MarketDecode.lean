import Benchmarks.Midnight.Common
import Benchmarks.Midnight.ABIHeadBounds

/-! Value-level decomposition of the modern ABI decoder used for stored markets. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

-- LIBRARY CANDIDATE: a single dynamic return value has one bounded relative offset.
theorem decodeDynamicReturnValue {ty : ABIType} {bytes : ByteArray}
    (hdyn : isDynamicABIType ty = true) (hsmall : bytes.size < 2^255) :
    decodeReturnValue? ty bytes = (do
      let off ← readNat? bytes.toList 0
      if solcMaxU64 < off then none else
        let value ← decodeABIValue? ty bytes.toList off
        pure value.1) := by
  have hb : ¬ 2^255 ≤ bytes.toList.length := by
    simp only [byteArray_toList_eq, Array.length_toList]
    exact Nat.not_le_of_lt hsmall
  simp only [decodeReturnValue?, decodeReturnValues?, List.isEmpty_cons, hb, and_false,
    if_false, abiTupleHeadSize?, hdyn, if_true, bind, Option.bind, pure,
    decodeABIValues?, solcMaxLen_modern, Nat.zero_add, Nat.add_zero]
  cases ho : readNat? bytes.toList 0 with
  | none => rfl
  | some off =>
    by_cases hcap : solcMaxU64 < off
    · simp only [hcap, if_true]
    · simp only [hcap, if_false]
      cases hv : decodeABIValue? ty bytes.toList off with
      | none => rfl
      | some pair => rcases pair with ⟨v, stop⟩; rfl

theorem readNat_bytes {bytes : ByteArray} {off : Nat} (h : off + 32 ≤ bytes.size) :
    readNat? bytes.toList off = some (calldataWord bytes off).toNat := by
  have hlen : ((bytes.toList.drop off).take 32).length = 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (bytes.size - off) = 32
    omega
  simp only [readNat?, readWord?, readBytes?, hlen, if_true, bind, Option.bind,
    decode_word_at_eq_any bytes off h]
  rfl

theorem readNat_bytes_short {bytes : ByteArray} {off : Nat} (h : bytes.size < off + 32) :
    readNat? bytes.toList off = none := by
  have hlen : ((bytes.toList.drop off).take 32).length ≠ 32 := by
    simp only [List.length_take, List.length_drop, byteArray_toList_eq, Array.length_toList]
    change min 32 (bytes.size - off) ≠ 32
    omega
  simp only [readNat?, readWord?, readBytes?, hlen, if_false, bind, Option.bind]

theorem decodeMarketRoot {bytes : ByteArray} (hsmall : bytes.size < 2^255) :
    config.externalABI.decodeValue? Model.marketABI bytes = (do
      let off ← readNat? bytes.toList 0
      if solcMaxU64 < off then none else
        let value ← decodeABIValue? Model.marketABI bytes.toList off
        pure value.1) := by
  exact decodeDynamicReturnValue rfl hsmall

theorem decodeMarketHead_bound {bytes : List UInt8} {start stop : Nat} {value : Value}
    (h : decodeABIValue? Model.marketABI bytes start = some (value, stop)) :
    start + 256 ≤ bytes.length := by
  rw [Model.marketABI, decodeABIValue?] at h
  have hh : abiTupleHeadSize? [Model.u256, Model.addr, Model.addr,
      .dynamicArray Model.collateralABI, Model.u256, Model.u256, Model.addr, Model.addr] =
      some 256 := by
    simp [abiTupleHeadSize?, Model.u256, Model.addr, isDynamicABIType, staticABIEncodedSize?]
  rw [hh] at h
  simp only [bind, Option.bind] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨⟨values, stop'⟩, hd, _⟩
  have hb := decodeABIWordHeads_bound (by
    simp only [List.forall_mem_cons]
    decide) hd
  rcases hb with hn | hb
  · cases hn
  · simpa using hb

theorem decodeMarketHead_short {bytes : List UInt8} {start : Nat}
    (hshort : bytes.length < start + 256) :
    decodeABIValue? Model.marketABI bytes start = none := by
  cases hd : decodeABIValue? Model.marketABI bytes start with
  | none => rfl
  | some pair =>
    have hb := decodeMarketHead_bound hd
    omega

theorem decodeMarketRoot_short {bytes : ByteArray} (hshort : bytes.size < 32) :
    config.externalABI.decodeValue? Model.marketABI bytes = none := by
  rw [decodeMarketRoot (by omega), readNat_bytes_short (by omega)]
  rfl

theorem decodeMarketRoot_largeOffset {bytes : ByteArray}
    (hsmall : bytes.size < 2^255) (hlen : 32 ≤ bytes.size)
    (hlarge : 2^64 ≤ (calldataWord bytes 0).toNat) :
    config.externalABI.decodeValue? Model.marketABI bytes = none := by
  rw [decodeMarketRoot hsmall, readNat_bytes hlen]
  simp only [bind, Option.bind]
  rw [if_pos (by change 18446744073709551615 < _; omega)]

theorem decodeMarketRoot_shortHead {bytes : ByteArray}
    (hsmall : bytes.size < 2^255) (hlen : 32 ≤ bytes.size)
    (hoff : (calldataWord bytes 0).toNat < 2^64)
    (hshort : bytes.size < (calldataWord bytes 0).toNat + 256) :
    config.externalABI.decodeValue? Model.marketABI bytes = none := by
  rw [decodeMarketRoot hsmall, readNat_bytes hlen]
  simp only [bind, Option.bind]
  rw [if_neg (by change ¬ 18446744073709551615 < _; omega), decodeMarketHead_short (by
    simpa only [byteArray_toList_eq, Array.length_toList] using hshort)]

end Benchmarks.Midnight
