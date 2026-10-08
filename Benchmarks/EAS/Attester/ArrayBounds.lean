import Benchmarks.EAS.Attester.ArrayDecodeTrace
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: turn a compiler uint64 guard into its natural-number bound.
theorem uint64Bound_of_isZero_gt {w : UInt256}
    (h : UInt256.isZero (UInt256.gt w (UInt256.ofNat 18446744073709551615)) ≠ UInt256.ofNat 0) :
    w.toNat ≤ ABI.solcMaxU64 := by
  have hb := ugt_eq_zero_to_le (u256_isZero_ne_zero_to_eq_zero h)
  exact hb

-- LIBRARY CANDIDATE: the address just after an array of EVM words.
theorem arrayEnd_toNat {head len : UInt256}
    (hfit : head.toNat + 32 + 32 * len.toNat < UInt256.size) :
    ((head + UInt256.shiftLeft len (UInt256.ofNat 5)) + UInt256.ofNat 32).toNat =
      head.toNat + 32 + 32 * len.toNat := by
  have hmul : 32 * len.toNat < UInt256.size := by omega
  have hshift : UInt256.shiftLeft len (UInt256.ofNat 5) = UInt256.ofNat (32 * len.toNat) := by
    conv_lhs => rw [← u256_ofNat_toNat len]
    exact shiftLeft5_ofNat_eq hmul
  rw [hshift, uadd_word_ofNat_toNat _ _ (by rw [uadd_word_ofNat_toNat _ _ (by omega)]; omega),
    uadd_word_ofNat_toNat _ _ (by omega)]
  omega

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

theorem ArrayHeadChecks.of_bounds {cd : ByteArray} {head : UInt256}
    (hsize : cd.size < 2 ^ 255)
    (hlen : (calldataWord cd head.toNat).toNat ≤ solcMaxU64)
    (hbound : head.toNat + 32 + 32 * (calldataWord cd head.toNat).toNat ≤ cd.size) :
    ArrayHeadChecks cd head := by
  have hfit : head.toNat + 32 + 32 * (calldataWord cd head.toNat).toNat < UInt256.size :=
    lt_of_le_of_lt hbound (lt_size_of_lt_sign hsize)
  constructor
  · rw [slt_lit_one_low hsize (by rw [uadd_word_ofNat_toNat _ _ (by omega)]; omega)]
    decide
  · rw [ugt_zero hlen]; decide
  · rw [ugt_zero (by rw [arrayEnd_toNat hfit, ulit_toNat' _ (lt_size_of_lt_sign hsize)]; exact
      hbound)]
    decide

theorem arrayHead_toNat {cd : ByteArray} {off : Nat}
    (h : (calldataWord cd off).toNat ≤ solcMaxU64) :
    (arrayHead cd off).toNat = 4 + (calldataWord cd off).toNat :=
  add4_word_toNat _ h

theorem arrayHead_data_toNat {cd : ByteArray} {off : Nat}
    (h : (calldataWord cd off).toNat ≤ solcMaxU64) :
    (arrayHead cd off + UInt256.ofNat 32).toNat = 4 + (calldataWord cd off).toNat + 32 := by
  have hfit : (arrayHead cd off).toNat + 32 < UInt256.size := by
    rw [arrayHead_toNat h]
    change 4 + (calldataWord cd off).toNat + 32 < 2 ^ 256
    change (calldataWord cd off).toNat ≤ 18446744073709551615 at h
    omega
  rw [uadd_word_ofNat_toNat _ _ hfit, arrayHead_toNat h]

theorem MultiHeadChecks.size_lt_sign {cd : ByteArray} (h : MultiHeadChecks cd)
    (hsize : cd.size < UInt256.size) : cd.size < 2 ^ 255 := by
  have hoff := uint64Bound_of_isZero_gt h.firstOffset
  by_contra hlarge
  have hz := calldataStart_slt_zero_of_size_high cd (Nat.not_lt.mpr hoff) hsize hlarge
  exact h.first.header hz

theorem MultiHeadChecks.head_size {cd : ByteArray} (h : MultiHeadChecks cd)
    (hsize : cd.size < UInt256.size) (hfour : 4 ≤ cd.size) : 68 ≤ cd.size := by
  by_contra hsmall
  have hz := solcDecodeLenCheckShort_4_64 hfour (by omega : cd.size < 68) hsize
  apply h.tuple
  change UInt256.isZero (UInt256.slt (UInt256.sub (UInt256.ofNat cd.size) ⟨4⟩) ⟨64⟩) = ⟨0⟩
  rw [hz]; rfl

theorem ArrayHeadChecks.outer_bounds {cd : ByteArray} {off : Nat}
    (h : ArrayHeadChecks cd (arrayHead cd off))
    (hoff : (calldataWord cd off).toNat ≤ solcMaxU64)
    (hsize : cd.size < UInt256.size) :
    4 + (calldataWord cd off).toNat + 32 +
      32 * (calldataWord cd (arrayHead cd off).toNat).toNat ≤ cd.size := by
  exact array_end_bound_of_ugt_zero (I := { (default : ExecutionEnv) with calldata := cd })
    hoff (uint64Bound_of_isZero_gt h.length)
    (u256_isZero_ne_zero_to_eq_zero h.payload) hsize

def arrayCount (cd : ByteArray) (off : Nat) : Nat :=
  (calldataWord cd (arrayHead cd off).toNat).toNat

def arrayDataNat (cd : ByteArray) (off : Nat) : Nat :=
  4 + (calldataWord cd off).toNat + 32

theorem arrayData_eq_ofNat {cd : ByteArray} {off : Nat}
    (h : (calldataWord cd off).toNat ≤ solcMaxU64) :
    arrayHead cd off + UInt256.ofNat 32 = UInt256.ofNat (arrayDataNat cd off) := by
  unfold arrayDataNat
  rw [← arrayHead_data_toNat h]
  exact (u256_ofNat_toNat _).symm

theorem arrayCount_word (cd : ByteArray) (off : Nat) :
    UInt256.ofNat (arrayCount cd off) = calldataWord cd (arrayHead cd off).toNat :=
  u256_ofNat_toNat _

end Benchmarks.EAS.Attester
