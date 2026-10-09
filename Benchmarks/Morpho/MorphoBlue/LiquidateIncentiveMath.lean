import Benchmarks.Morpho.MorphoBlue.MinWord
import Benchmarks.Morpho.MorphoBlue.WadDivDownSource
import Benchmarks.Morpho.MorphoBlue.HealthyLocals

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

def liquidationCursor : UInt256 := UInt256.ofNat 300000000000000000
def liquidationCap : UInt256 := UInt256.ofNat 1150000000000000000
def liquidationDiscount (lltv : UInt256) : UInt256 :=
  wMulDownResult liquidationCursor (UInt256.sub wad lltv)
def liquidationDenom (lltv : UInt256) : UInt256 := UInt256.sub wad (liquidationDiscount lltv)
def liquidationFactor (lltv : UInt256) : UInt256 :=
  minWord liquidationCap (wDivDownResult wad (liquidationDenom lltv))

theorem liquidationDiscount_mul_fits {lltv : UInt256} (h : lltv.toNat ≤ wad.toNat) :
    liquidationCursor.toNat * (UInt256.sub wad lltv).toNat < UInt256.size := by
  rw [usub_toNat h]
  have hh : wad.toNat - lltv.toNat ≤ 1000000000000000000 := Nat.sub_le _ _
  have hm := Nat.mul_le_mul_left 300000000000000000 hh
  change 300000000000000000 * (1000000000000000000 - lltv.toNat) < 2 ^ 256
  omega

theorem liquidationDiscount_bound {lltv : UInt256} (h : lltv.toNat ≤ wad.toNat) :
    (liquidationDiscount lltv).toNat ≤ 300000000000000000 := by
  rw [liquidationDiscount, wMulDownResult, udiv_toNat, u256_mul_toNat,
    Nat.mod_eq_of_lt (liquidationDiscount_mul_fits h), usub_toNat h]
  have hm := Nat.mul_le_mul_left 300000000000000000 (Nat.sub_le wad.toNat lltv.toNat)
  have hd := Nat.div_le_div_right (c := 1000000000000000000) hm
  exact hd

theorem liquidationDenom_bounds {lltv : UInt256} (h : lltv.toNat ≤ wad.toNat) :
    700000000000000000 ≤ (liquidationDenom lltv).toNat ∧ (liquidationDenom lltv).toNat ≤ wad.toNat := by
  have hb := liquidationDiscount_bound h
  have hl : (liquidationDiscount lltv).toNat ≤ wad.toNat := by change _ ≤ 1000000000000000000; omega
  rw [liquidationDenom, usub_toNat hl]
  change 700000000000000000 ≤ 1000000000000000000 - (liquidationDiscount lltv).toNat ∧
    1000000000000000000 - (liquidationDiscount lltv).toNat ≤ 1000000000000000000
  omega

theorem liquidationDenom_ne_zero {lltv : UInt256} (h : lltv.toNat ≤ wad.toNat) :
    liquidationDenom lltv ≠ ⟨0⟩ := by
  intro hz
  have hb := (liquidationDenom_bounds h).1
  rw [hz] at hb
  contradiction

theorem liquidationFactor_positive {lltv : UInt256} (h : lltv.toNat ≤ wad.toNat) :
    0 < (liquidationFactor lltv).toNat := by
  have hb := liquidationDenom_bounds h
  have hn : (liquidationDenom lltv).toNat ≤ (UInt256.mul wad wad).toNat := by
    have hm : (UInt256.mul wad wad).toNat = 1000000000000000000000000000000000000 := by decide
    rw [hm]; have hh := hb.2; change _ ≤ 1000000000000000000 at hh; omega
  have hd := Nat.div_pos hn (by omega : 0 < (liquidationDenom lltv).toNat)
  unfold liquidationFactor minWord
  split
  · change 0 < 1150000000000000000; omega
  · rw [wDivDownResult, udiv_toNat]; exact hd

theorem liquidationWadSquare : UInt256.mul wad wad = oraclePriceScale := by decide

end Benchmarks.Morpho.MorphoBlue
