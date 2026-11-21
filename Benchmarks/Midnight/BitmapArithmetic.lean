import Benchmarks.Midnight.PackedWrites
import Benchmarks.Midnight.Uint128Arithmetic
import Mathlib.Data.Nat.Size

/-! Highest-bit indices and progress of the collateral bitmap loop. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def bitmapMsb (bitmap : UInt256) : UInt256 :=
  UInt256.sub (UInt256.ofNat 255) (UInt256.clz bitmap)

def bitmapClear (bitmap bit : UInt256) : UInt256 :=
  low128 (UInt256.land bitmap (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1) bit)))

-- LIBRARY CANDIDATE: relate the EVM highest-bit idiom to the natural logarithm.
theorem bitmapMsb_toNat {bitmap : UInt256} (hn : bitmap.toNat ≠ 0) :
    (bitmapMsb bitmap).toNat = bitmap.toNat.log2 := by
  have hl : bitmap.toNat.log2 < 256 := (Nat.log2_lt hn).mpr bitmap.val.isLt
  have hc : (UInt256.clz bitmap).toNat = 255 - bitmap.toNat.log2 := by
    rw [UInt256.clz, if_neg hn, UInt256.toNat_ofNat_of_lt (by change _ < 2^256; omega)]
  rw [bitmapMsb, usub_toNat (by rw [hc]; change _ ≤ 255; omega), hc]
  change 255 - (255 - bitmap.toNat.log2) = bitmap.toNat.log2
  omega

theorem bitmapMsb_lt {bitmap : UInt256} {bits : Nat}
    (hn : bitmap.toNat ≠ 0) (hb : bitmap.toNat < 2^bits) :
    (bitmapMsb bitmap).toNat < bits := by
  rw [bitmapMsb_toNat hn]
  exact (Nat.log2_lt hn).mpr hb

-- LIBRARY CANDIDATE: clearing the highest set bit removes every bit at that height or above.
theorem bitmapClear_msb_lt {bitmap : UInt256} (hn : bitmap.toNat ≠ 0) :
    (bitmapClear bitmap (bitmapMsb bitmap)).toNat < 2^(bitmapMsb bitmap).toNat := by
  let i := bitmap.toNat.log2
  have hi : i < 256 := (Nat.log2_lt hn).mpr bitmap.val.isLt
  have hp : 2^i < UInt256.size := Nat.pow_lt_pow_right (by decide) hi
  have hpow : (UInt256.shiftLeft (UInt256.ofNat 1) (bitmapMsb bitmap)).toNat = 2^i := by
    rw [shiftLeft_toNat_of_noOverflow _ _ (by rw [bitmapMsb_toNat hn]; exact hi)
      (by rw [bitmapMsb_toNat hn]; simpa only [show (UInt256.ofNat 1).toNat = 1 from rfl,
        Nat.one_mul] using hp), bitmapMsb_toNat hn]
    exact Nat.one_mul _
  have htop : bitmap.toNat < 2^(i+1) := (Nat.log2_eq_iff hn).mp rfl |>.2
  have hclear : (UInt256.land bitmap
      (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 1) (bitmapMsb bitmap)))).toNat < 2^i := by
    rw [uland_toNat, lnot_toNat_gen, hpow]
    apply Nat.lt_pow_two_of_testBit
    intro j hj
    rw [Nat.testBit_and]
    by_cases he : j = i
    · subst j
      rw [show 2^256 - 1 - 2^i = 2^256 - (2^i + 1) by omega,
        Nat.testBit_two_pow_sub_succ hp, Nat.testBit_two_pow_self]
      simp
    · have hh : bitmap.toNat < 2^j :=
        htop.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
      rw [Nat.testBit_lt_two_pow hh, Bool.false_and]
  rw [bitmapClear, low128_toNat, bitmapMsb_toNat hn]
  exact (Nat.mod_le _ _).trans_lt hclear

-- LIBRARY CANDIDATE: number of right shifts needed to clear a natural-number bitmap.
theorem natSize_eq_log2_succ {n : Nat} (hn : n ≠ 0) : n.size = n.log2 + 1 := by
  have hlo := (Nat.lt_size).mpr ((Nat.log2_eq_iff hn).mp rfl).1
  have hhi := (Nat.size_le).mpr ((Nat.log2_eq_iff hn).mp rfl).2
  omega

theorem natSize_div_two {n : Nat} (hn : n ≠ 0) : n.size = (n / 2).size + 1 := by
  have hb : Nat.bit n.bodd n.div2 = n := Nat.bit_bodd_div2 n
  rw [← hb, Nat.size_bit (by rw [hb]; exact hn)]
  rw [hb]
  simp only [Nat.div2_val, Nat.succ_eq_add_one]

end Benchmarks.Midnight
