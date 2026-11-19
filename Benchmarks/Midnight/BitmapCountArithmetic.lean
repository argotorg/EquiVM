import Benchmarks.Midnight.BitmapArithmetic

/-! The word program used by the bitmap setter and population-count helper. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def bitmapSet (bitmap bit : UInt256) : UInt256 :=
  low128 (UInt256.lor bitmap (UInt256.shiftLeft (UInt256.ofNat 1) bit))

abbrev countMask1 : UInt256 := UInt256.ofNat 113427455640312821154458202477256070485
abbrev countMask2 : UInt256 := UInt256.ofNat 68056473384187692692674921486353642291
abbrev countMask4 : UInt256 := UInt256.ofNat 20016609818878733144904388672456953615
abbrev countMultiplier : UInt256 := UInt256.ofNat 1334440654591915542993625911497130241

def bitmapCount1 (x : UInt256) : UInt256 :=
  UInt256.sub x (UInt256.land (UInt256.shiftRight x (UInt256.ofNat 1)) countMask1)

def bitmapCount2 (x : UInt256) : UInt256 :=
  UInt256.land x countMask2 + UInt256.land (UInt256.shiftRight x (UInt256.ofNat 2)) countMask2

def bitmapCount4 (x : UInt256) : UInt256 :=
  UInt256.land (low128 (x + UInt256.shiftRight x (UInt256.ofNat 4))) countMask4

def bitmapCount (x : UInt256) : UInt256 :=
  UInt256.shiftRight (low128 (UInt256.mul (bitmapCount4 (bitmapCount2 (bitmapCount1 x)))
    countMultiplier)) (UInt256.ofNat 120)

theorem bitmapSet_clean {bitmap bit : UInt256}
    (hb : bitmap.toNat < 2^128) (hi : bit.toNat < 128) :
    bitmapSet bitmap bit = UInt256.lor (UInt256.shiftLeft (UInt256.ofNat 1) bit) bitmap := by
  rw [bitmapSet, low128, uint128Mask_clean, u256_lor_comm]
  rw [u256_lor_toNat_exact]
  apply Nat.or_lt_two_pow hb
  rw [shiftLeft_toNat_of_noOverflow _ _ (by omega) (by
    change 1 * 2^bit.toNat < 2^256
    simpa only [Nat.one_mul] using Nat.pow_lt_pow_right (a := 2) (by decide) (by omega : bit.toNat < 256))]
  change 1 * 2^bit.toNat < 2^128
  simpa only [Nat.one_mul] using Nat.pow_lt_pow_right (a := 2) (by decide) hi

theorem bitmapCount1_sub_le (x : UInt256) :
    (UInt256.land (UInt256.shiftRight x (UInt256.ofNat 1)) countMask1).toNat ≤ x.toNat := by
  rw [uland_toNat]
  apply Nat.and_le_left.trans
  rw [shiftRight_toNat _ _ (by decide)]
  exact Nat.div_le_self _ _

theorem bitmapCount1_lt {x : UInt256} (hx : x.toNat < 2^128) :
    (bitmapCount1 x).toNat < 2^128 := by
  rw [bitmapCount1, usub_toNat (bitmapCount1_sub_le x)]
  omega

theorem bitmapCount2_lt (x : UInt256) : (bitmapCount2 x).toNat < 2^128 := by
  have h1 : (UInt256.land x countMask2).toNat ≤ countMask2.toNat := by
    rw [uland_toNat]; exact Nat.and_le_right
  have h2 : (UInt256.land (UInt256.shiftRight x (UInt256.ofNat 2)) countMask2).toNat ≤
      countMask2.toNat := by rw [uland_toNat]; exact Nat.and_le_right
  rw [bitmapCount2, uadd_toNat]
  have hm := Nat.mod_le ((UInt256.land x countMask2).toNat +
    (UInt256.land (UInt256.shiftRight x (UInt256.ofNat 2)) countMask2).toNat) UInt256.size
  change _ ≤ 68056473384187692692674921486353642291 at h1 h2
  omega

theorem bitmapCount4_lt (x : UInt256) : (bitmapCount4 x).toNat < 2^128 := by
  unfold bitmapCount4
  rw [uland_toNat]
  exact Nat.and_le_left.trans_lt (low128_lt _)

theorem wordAnd_assoc (a b c : UInt256) :
    UInt256.land (UInt256.land a b) c = UInt256.land a (UInt256.land b c) := by
  apply u256_inj
  simp only [uland_toNat, Nat.and_assoc]

theorem low128_and_clean {a b : UInt256} (hb : b.toNat < 2^128) :
    UInt256.land (low128 a) b = UInt256.land a b := by
  rw [low128, wordAnd_assoc, u256_land_comm uint128Mask, uint128Mask_clean hb]

theorem bitmapCount4_raw (x : UInt256) :
    bitmapCount4 x = UInt256.land (x + UInt256.shiftRight x (UInt256.ofNat 4)) countMask4 :=
  low128_and_clean (by decide)

theorem wordShiftRight_and (a b shift : UInt256) (hs : shift.toNat < 256) :
    UInt256.shiftRight (UInt256.land a b) shift =
      UInt256.land (UInt256.shiftRight a shift) (UInt256.shiftRight b shift) := by
  apply u256_inj
  simp only [shiftRight_toNat _ _ hs, uland_toNat]
  simpa only [Nat.shiftRight_eq_div_pow] using
    (Nat.shiftRight_and_distrib (a := a.toNat) (b := b.toNat) (i := shift.toNat))

theorem bitmapCount_raw (x : UInt256) : bitmapCount x =
    UInt256.land (UInt256.shiftRight
      (UInt256.mul (bitmapCount4 (bitmapCount2 (bitmapCount1 x))) countMultiplier)
      (UInt256.ofNat 120)) (UInt256.ofNat 255) := by
  unfold bitmapCount low128
  rw [wordShiftRight_and _ _ _ (by decide)]
  rfl

theorem bitmapCount2_shift_mask (x : UInt256) :
    UInt256.land (UInt256.shiftRight (bitmapCount2 x) (UInt256.ofNat 4))
      (UInt256.ofNat 21267647932558653966460912964485513215) =
      UInt256.shiftRight (bitmapCount2 x) (UInt256.ofNat 4) := by
  apply u256LandMaskCleanOfToNat (bits := 124) _ _ (by decide)
  rw [shiftRight_toNat _ _ (by decide)]
  have hx := bitmapCount2_lt x
  change (bitmapCount2 x).toNat / 16 < 2^124
  omega

end Benchmarks.Midnight
