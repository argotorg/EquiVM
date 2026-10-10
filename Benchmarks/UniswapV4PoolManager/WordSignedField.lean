import Benchmarks.UniswapV4PoolManager.WordFillHigh

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- GENERALIZES wordSignBit24 to every bit of an EVM word.
theorem wordSignBitRange (w : UInt256) {n : Nat} (hn : n < 256) :
    UInt256.land w (UInt256.ofNat (2^n)) ≠ ⟨0⟩ ↔ 2^n ≤ w.toNat % 2^(n+1) := by
  have hp : 2^n < UInt256.size := Nat.pow_lt_pow_right (by decide) hn
  have hm : (UInt256.land w (UInt256.ofNat (2^n))).toNat =
      (w.toNat.testBit n).toNat * 2^n := by
    rw [uland_toNat, UInt256.toNat_ofNat_of_lt hp, Nat.and_two_pow]
  have hz : UInt256.land w (UInt256.ofNat (2^n)) = ⟨0⟩ ↔
      (UInt256.land w (UInt256.ofNat (2^n))).toNat = 0 := by
    constructor
    · intro he; rw [he]; rfl
    · exact uint256_toNat_eq_zero
  have hb : (w.toNat % 2^(n+1)).testBit n = w.toNat.testBit n := by
    rw [Nat.testBit_mod_two_pow]
    simp only [show n < n+1 by omega, decide_true, Bool.true_and]
  rw [ne_eq, hz, hm, ← hb]
  by_cases hh : 2^n ≤ w.toNat % 2^(n+1)
  · rw [Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt hh (Nat.mod_lt _ (Nat.two_pow_pos _))]
    simp only [Bool.toNat_true, one_mul, Nat.ne_of_gt (Nat.two_pow_pos n), not_false_eq_true, hh]
  · rw [Nat.testBit_lt_two_pow (Nat.lt_of_not_ge hh)]
    simp only [Bool.toNat_false, zero_mul, not_true_eq_false, hh]

-- LIBRARY CANDIDATE: signed words preserve their residues at every valid ABI integer width.
theorem signedWordResidue (bits : BitWidth) (w : UInt256) :
    EVM.signed w % Int.ofNat (2^bits.val) = Int.ofNat (w.toNat % 2^bits.val) := by
  have hd : (2 : Int)^bits.val ∣ (2 : Int)^256 := pow_dvd_pow (2 : Int) bits.property.2.1
  have hw := normalizeUnsignedSigned w
  change EVM.signed w % (2^256 : Int) = Int.ofNat w.toNat at hw
  simp only [Int.ofNat_eq_natCast, Int.natCast_pow, Int.cast_ofNat_Int, Int.natCast_emod]
  calc
    _ = (EVM.signed w % (2^256 : Int)) % (2 : Int)^bits.val := (Int.emod_emod_of_dvd _ hd).symm
    _ = _ := by rw [hw]; rfl

-- GENERALIZES normalizeSigned24Word and normalizeSigned128Word to arbitrary signed fields.
-- LIBRARY CANDIDATE: signed normalization is a sign-bit test followed by filling or clearing high bits.
theorem normalizeSignedFieldWord (bits : BitWidth) (w : UInt256) :
    normalizeInt (.sint bits) (EVM.signed w) = EVM.signed
      (if UInt256.land w (UInt256.ofNat (2^(bits.val-1))) ≠ ⟨0⟩ then
        UInt256.lor w (UInt256.ofNat (2^256-2^(bits.val-1)))
       else UInt256.land w (UInt256.ofNat (2^(bits.val-1)-1))) := by
  let n := bits.val-1
  have hn : n < 256 := by have := bits.property; dsimp only [n]; omega
  have hwidth : bits.val = n+1 := by have := bits.property; dsimp only [n]; omega
  have hp : 0 < 2^n := Nat.two_pow_pos _
  have hple : 2^n ≤ 2^255 := Nat.pow_le_pow_right (by decide) (by omega)
  have hw : w.toNat < 2^256 := w.val.isLt
  have hr := signedWordResidue bits w
  rw [hwidth] at hr
  have hpow : 2^(n+1) = 2^n*2 := Nat.pow_succ 2 n
  have hmod : w.toNat % 2^(n+1) < 2^n*2 := by
    rw [← hpow]; exact Nat.mod_lt _ (Nat.two_pow_pos _)
  have hsmall : w.toNat % 2^n < 2^n := Nat.mod_lt _ hp
  have hnest : (w.toNat % 2^(n+1)) % 2^n = w.toNat % 2^n :=
    Nat.mod_mod_of_dvd _ (pow_dvd_pow 2 (by omega))
  simp only [normalizeInt, EVM.twoPow]
  rw [hwidth]
  simp only [Nat.add_sub_cancel]
  rw [hr]
  simp only [Int.ofNat_eq_natCast]
  by_cases hh : 2^n ≤ w.toNat % 2^(n+1)
  · rw [if_neg (by exact not_lt.mpr (Int.ofNat_le.mpr hh)), if_pos ((wordSignBitRange w hn).mpr hh)]
    have hv : (UInt256.lor w (UInt256.ofNat (2^256-2^n))).toNat = 2^256-2^n+w.toNat%2^n := by
      rw [u256_lor_toNat_exact, UInt256.toNat_ofNat_of_lt (show 2^256-2^n < UInt256.size by
        change 2^256-2^n < 2^256; omega)]
      exact natOrFillHigh (by omega) hw
    have hm : w.toNat % 2^n = w.toNat % 2^(n+1)-2^n := by
      rw [← hnest, Nat.mod_eq_sub_mod hh, Nat.mod_eq_of_lt (by omega)]
    have hsum : w.toNat % 2^(n+1) = w.toNat % 2^n + 2^n := by omega
    change ((w.toNat % 2^(n+1) : Nat) : Int) - ((2^(n+1) : Nat) : Int) =
      (if (UInt256.lor w (UInt256.ofNat (2^256-2^n))).toNat < 2^255 then
        ((UInt256.lor w (UInt256.ofNat (2^256-2^n))).toNat : Int) else
        ((UInt256.lor w (UInt256.ofNat (2^256-2^n))).toNat : Int) - (2^256 : Int))
    rw [hv, if_neg (by omega), hsum, hpow]
    simp only [Int.natCast_add, Int.natCast_mul, Int.natCast_sub (show 2^n ≤ 2^256 by omega)]
    omega
  · rw [if_pos (Int.ofNat_lt.mpr (Nat.lt_of_not_ge hh)), if_neg (fun he => hh ((wordSignBitRange w hn).mp he))]
    have hv : (UInt256.land w (UInt256.ofNat (2^n-1))).toNat = w.toNat%2^n := by
      rw [uland_toNat, UInt256.toNat_ofNat_of_lt (show 2^n-1 < UInt256.size by
        change 2^n-1 < 2^256; omega)]
      exact nat_land_mask_eq_mod _ _
    have hm : w.toNat % 2^n = w.toNat % 2^(n+1) := by
      rw [← hnest, Nat.mod_eq_of_lt (Nat.lt_of_not_ge hh)]
    change ((w.toNat % 2^(n+1) : Nat) : Int) =
      (if (UInt256.land w (UInt256.ofNat (2^n-1))).toNat < 2^255 then
        ((UInt256.land w (UInt256.ofNat (2^n-1))).toNat : Int) else
        ((UInt256.land w (UInt256.ofNat (2^n-1))).toNat : Int) - (2^256 : Int))
    rw [hv, if_pos (by omega), hm]

end Benchmarks.UniswapV4PoolManager
