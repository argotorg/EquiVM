import Benchmarks.Midnight.CalldataBounds
import Benchmarks.Midnight.MemoryArrayIndex

/-! Bounds for calldata byte slices and arrays of scalar words. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def calldataSliceStride (isBytes : Bool) : Nat := if isBytes then 1 else 32

def CalldataSliceValid (isBytes : Bool) (bytes : ByteArray) (head : UInt256) : Prop :=
  bytes.size < 2^255 ∧ head.toNat + 32 ≤ bytes.size ∧
    (calldataWord bytes head.toNat).toNat < 2^64 ∧
    head.toNat + 32 + calldataSliceStride isBytes *
      (calldataWord bytes head.toNat).toNat ≤ bytes.size

def calldataSliceEndWord (isBytes : Bool) (head len : UInt256) : UInt256 :=
  if isBytes then head + len + UInt256.ofNat 32
  else UInt256.shiftLeft len (UInt256.ofNat 5) + head + UInt256.ofNat 32

theorem calldataSliceEnd_toNat (isBytes : Bool) {head len : UInt256}
    (hh : head.toNat < 2^128) (hl : len.toNat < 2^64) :
    (calldataSliceEndWord isBytes head len).toNat =
      head.toNat + 32 + calldataSliceStride isBytes * len.toNat := by
  cases isBytes
  · change (UInt256.shiftLeft len (UInt256.ofNat 5) + head + UInt256.ofNat 32).toNat =
      head.toNat + 32 + 32 * len.toNat
    rw [arrayIndexWord hl, wordAddNat_add,
      uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)]
    omega
  · have hadd : (head + len).toNat = head.toNat + len.toNat := by
      rw [uadd_toNat, Nat.mod_eq_of_lt (by change _ < 2^256; omega)]
    change (head + len + UInt256.ofNat 32).toNat = head.toNat + 32 + 1 * len.toNat
    rw [uadd_word_ofNat_toNat _ _ (by rw [hadd]; change _ < 2^256; omega), hadd]
    omega

theorem calldataSliceHeaderCheck {bytes : ByteArray} {head : UInt256}
    (hh : head.toNat < 2^128) (hsize : bytes.size < UInt256.size) :
    UInt256.slt (head + UInt256.ofNat 31) (UInt256.ofNat bytes.size) =
      UInt256.fromBool (decide (bytes.size < 2^255 ∧ head.toNat + 32 ≤ bytes.size)) := by
  have hn : (head + UInt256.ofNat 31).toNat = head.toNat + 31 :=
    uadd_word_ofNat_toNat _ _ (by change _ < 2^256; omega)
  by_cases hs : bytes.size < 2^255
  · by_cases hb : head.toNat + 32 ≤ bytes.size
    · simp only [hs, hb, and_self, decide_true]
      exact slt_lit_one_low hs (by rw [hn]; omega)
    · simp only [hs, hb, and_false, decide_false]
      exact slt_lit_zero hs (by rw [hn]; omega) (by rw [hn]; omega)
  · simp only [hs, false_and, decide_false]
    exact slt_zero_low_high (by rw [hn]; omega)
      (by rw [UInt256.toNat_ofNat_of_lt hsize]; omega)

end Benchmarks.Midnight
