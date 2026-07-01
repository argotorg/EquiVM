import Reasoning.Theory
import Mathlib.Data.Nat.Bitwise
import Mathlib.Data.Nat.Digits.Defs
import Mathlib.Data.Nat.Digits.Lemmas

/-!
# EVMWord — arithmetic facts for EVM 256-bit stack words

The EVM executes arithmetic and comparisons on 256-bit stack words, even when the Solidity source
type is narrower.  This file collects generic `UInt256` facts used by bytecode traces: no-wrap
`toNat` lemmas, unsigned comparisons, and signed `SLT` facts parameterized by the comparison
literal.  Memory byte-level facts stay in `Reasoning.Memory`; solc conventions stay in
`Reasoning.Solc`.
-/

open Ethereum Ethereum.EVM

namespace Reasoning.Theory

/-! ## Word reconstruction and no-wrap arithmetic -/

/-- `AccountAddress.ofUInt256` is the same address as taking the word's natural value. -/
theorem accountAddress_ofUInt256_eq_ofNat_toNat (w : UInt256) :
    AccountAddress.ofUInt256 w = AccountAddress.ofNat w.toNat := by
  apply Fin.ext
  simp [AccountAddress.ofUInt256, AccountAddress.ofNat, UInt256.toNat]

/-- `UInt256` is determined by its `toNat`. -/
theorem u256_inj {a b : UInt256} (h : a.toNat = b.toNat) : a = b := by
  cases a; cases b; simp only [UInt256.toNat] at h; exact congrArg UInt256.mk (Fin.ext h)

/-- Rebuilding a word from its in-range `toNat` gives the same word. -/
theorem u256_ofNat_toNat (a : UInt256) : UInt256.ofNat a.toNat = a := by
  apply u256_inj
  show (Fin.ofNat _ a.toNat).val = a.toNat
  simp only [Fin.ofNat]
  exact Nat.mod_eq_of_lt a.val.isLt

/-- Any `n < 2^255` fits in an EVM word. -/
theorem lt_size_of_lt_sign {n : ℕ} (h : n < 2 ^ 255) : n < UInt256.size := by
  have hsign : (2 : ℕ) ^ 255 < UInt256.size := by norm_num [UInt256.size]
  omega

/-- `(ofNat c).toNat = c` for an in-range literal `c`. -/
theorem ulit_toNat' (c : ℕ) (h : c < UInt256.size) : (UInt256.ofNat c).toNat = c := by
  show (Fin.ofNat _ c).val = c
  simp only [Fin.ofNat]
  exact Nat.mod_eq_of_lt h

theorem umin_ofNat_right_toNat_of_ge {c n : ℕ}
    (hc : c < UInt256.size) (hlo : c ≤ n) (hhi : n < UInt256.size) :
    (min (UInt256.ofNat c) (UInt256.ofNat n)).toNat = c := by
  show (if UInt256.ofNat c ≤ UInt256.ofNat n then UInt256.ofNat c else UInt256.ofNat n).toNat = c
  rw [if_pos]
  · exact ulit_toNat' c hc
  · show (UInt256.ofNat c).toNat ≤ (UInt256.ofNat n).toNat
    rw [ulit_toNat' c hc, ulit_toNat' n hhi]
    exact hlo

theorem umin_ofNat_right_toNat_of_lt {c n : ℕ}
    (hc : c < UInt256.size) (hn : n < c) (hhi : n < UInt256.size) :
    (min (UInt256.ofNat c) (UInt256.ofNat n)).toNat = n := by
  show (if UInt256.ofNat c ≤ UInt256.ofNat n then UInt256.ofNat c else UInt256.ofNat n).toNat = n
  rw [if_neg]
  · exact ulit_toNat' n hhi
  · show ¬ (UInt256.ofNat c).toNat ≤ (UInt256.ofNat n).toNat
    rw [ulit_toNat' c hc, ulit_toNat' n hhi]
    omega

/-- General `ADD` `toNat` (mod `size`). -/
theorem uadd_toNat (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % UInt256.size := by
  show (a.val + b.val).val = (a.val.val + b.val.val) % UInt256.size
  rw [Fin.add_def]

theorem uadd_lit32_toNat (a : UInt256) (h : a.toNat + 32 < UInt256.size) :
    (((⟨32⟩ : UInt256) + a).toNat = a.toNat + 32) := by
  rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  have hcomm : 32 + a.toNat = a.toNat + 32 := by omega
  rw [hcomm, Nat.mod_eq_of_lt h]

theorem uadd_word_lit32_toNat (a : UInt256) (h : a.toNat + 32 < UInt256.size) :
    ((a + (⟨32⟩ : UInt256)).toNat = a.toNat + 32) := by
  rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide,
    Nat.mod_eq_of_lt h]

/-- General `SUB` `toNat` (no wrap, given `b ≤ a`). -/
theorem usub_toNat {a b : UInt256} (h : b.toNat ≤ a.toNat) :
    (UInt256.sub a b).toNat = a.toNat - b.toNat := by
  show (a.val - b.val).val = a.toNat - b.toNat
  rw [Fin.coe_sub_iff_le.mpr (by rw [Fin.le_def]; exact h)]
  rfl

/-- General `SUB` `toNat` (wrapping, given `a < b`). -/
theorem usub_toNat_underflow {a b : UInt256} (h : a.toNat < b.toNat) :
    (UInt256.sub a b).toNat = UInt256.size + a.toNat - b.toNat := by
  show (a.val - b.val).val = UInt256.size + a.toNat - b.toNat
  rw [Fin.coe_sub_iff_lt.mpr (by rw [Fin.lt_def]; exact h)]
  rfl

/-- Subtracting a word from itself gives zero. -/
theorem u256_sub_self (w : UInt256) : UInt256.sub w w = ⟨0⟩ := by
  apply u256_inj
  rw [usub_toNat (a := w) (b := w) le_rfl, Nat.sub_self]
  rfl

/-- Subtracting distinct words cannot give zero. -/
theorem u256_sub_ne_zero_of_ne {a b : UInt256} (h : a ≠ b) :
    UInt256.sub a b ≠ ⟨0⟩ := by
  intro hz
  by_cases hle : b.toNat ≤ a.toNat
  · have hsub := usub_toNat (a := a) (b := b) hle
    rw [hz] at hsub
    have hzero : a.toNat - b.toNat = 0 := hsub.symm
    have hnat : a.toNat = b.toNat := by omega
    apply h
    apply u256_inj
    exact hnat
  · have hlt : a.toNat < b.toNat := Nat.lt_of_not_ge hle
    have hsub := usub_toNat_underflow (a := a) (b := b) hlt
    rw [hz] at hsub
    have hb : b.toNat < UInt256.size := b.val.isLt
    have hzero : UInt256.size + a.toNat - b.toNat = 0 := hsub.symm
    have hpos : 0 < UInt256.size + a.toNat - b.toNat := by omega
    omega

/-- Subtracting a nonzero word from zero cannot give zero. -/
theorem u256_zero_sub_ne_zero {w : UInt256} (h : w ≠ ⟨0⟩) :
    UInt256.sub ⟨0⟩ w ≠ ⟨0⟩ := by
  intro hz
  have htoNat : w.toNat ≠ 0 := by
    intro hnat
    apply h
    apply u256_inj
    exact hnat
  have hpos : 0 < w.toNat := Nat.pos_of_ne_zero htoNat
  have hsub := usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w) hpos
  rw [hz] at hsub
  have hwlt : w.toNat < UInt256.size := w.val.isLt
  have hgt : 0 < UInt256.size + (⟨0⟩ : UInt256).toNat - w.toNat := by
    omega
  omega

/-- `ADD` of two in-range naturals does not wrap. -/
theorem uadd_ofNat_toNat {a b : ℕ}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hab : a + b < UInt256.size) :
    (UInt256.add (UInt256.ofNat a) (UInt256.ofNat b)).toNat = a + b := by
  rw [show UInt256.add (UInt256.ofNat a) (UInt256.ofNat b)
        = UInt256.ofNat a + UInt256.ofNat b from rfl,
      uadd_toNat, ulit_toNat' a ha, ulit_toNat' b hb, Nat.mod_eq_of_lt hab]

/-- `SUB` of `ofNat n` and an in-range literal `c` is `n - c`, assuming no underflow. -/
theorem usub_ofNat_lit_toNat {n c : ℕ} (hc : c ≤ n) (hn : n < UInt256.size) :
    (UInt256.sub (UInt256.ofNat n) (UInt256.ofNat c)).toNat = n - c := by
  have hcn : c < UInt256.size := lt_of_le_of_lt hc hn
  rw [show UInt256.sub (UInt256.ofNat n) (UInt256.ofNat c)
        = UInt256.ofNat n - UInt256.ofNat c from rfl,
      UInt256.toNat_sub_ofNat_of_le (by rw [ulit_toNat' n hn]; exact hc),
      ulit_toNat' n hn]

/-- `SUB` of `ofNat n` and a word literal is `n - c.toNat`, assuming no underflow. -/
theorem usub_ofNat_word_toNat {n : ℕ} {c : UInt256} (hc : c.toNat ≤ n) (hn : n < UInt256.size) :
    (UInt256.sub (UInt256.ofNat n) c).toNat = n - c.toNat := by
  rw [usub_toNat (a := UInt256.ofNat n) (b := c) (by rw [ulit_toNat' n hn]; exact hc),
      ulit_toNat' n hn]

/-- `head + (size - head) = size` for non-wrapping word arithmetic. -/
theorem uadd_lit_usub_ofNat_lit {n c : ℕ} (hc : c ≤ n) (hn : n < UInt256.size) :
    (UInt256.ofNat c + UInt256.sub (UInt256.ofNat n) (UInt256.ofNat c)) = UInt256.ofNat n := by
  apply u256_inj
  have hcn : c < UInt256.size := lt_of_le_of_lt hc hn
  rw [uadd_toNat, ulit_toNat' c hcn, usub_ofNat_lit_toNat hc hn, ulit_toNat' n hn,
      show c + (n - c) = n from by omega, Nat.mod_eq_of_lt hn]

/-- `head + (size - head) = size` for a word-valued head pointer. -/
theorem uadd_word_usub_ofNat_word {n : ℕ} {c : UInt256} (hc : c.toNat ≤ n) (hn : n < UInt256.size) :
    c + UInt256.sub (UInt256.ofNat n) c = UInt256.ofNat n := by
  apply u256_inj
  rw [uadd_toNat, usub_ofNat_word_toNat hc hn, ulit_toNat' n hn,
      show c.toNat + (n - c.toNat) = n from by omega, Nat.mod_eq_of_lt hn]

/-- `(base + n) - base = n` when the addition does not wrap. -/
theorem usub_uadd_lit_cancel {base n : ℕ}
    (hbase : base < UInt256.size) (hn : n < UInt256.size)
    (hadd : base + n < UInt256.size) :
    UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat n)) (UInt256.ofNat base)
      = UInt256.ofNat n := by
  apply u256_inj
  have haddn : (UInt256.add (UInt256.ofNat base) (UInt256.ofNat n)).toNat = base + n :=
    uadd_ofNat_toNat hbase hn hadd
  rw [show UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat n)) (UInt256.ofNat base)
        = UInt256.add (UInt256.ofNat base) (UInt256.ofNat n) - UInt256.ofNat base from rfl,
      UInt256.toNat_sub_ofNat_of_le (by rw [haddn]; omega), haddn, ulit_toNat' n hn]
  omega

/-- `(base + n) - base = n` in word arithmetic, allowing the addition to wrap. -/
theorem usub_uadd_lit_cancel_mod {base n : ℕ}
    (hbase : base < UInt256.size) (hn : n < UInt256.size) :
    UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat n)) (UInt256.ofNat base)
      = UInt256.ofNat n := by
  apply u256_inj
  by_cases hadd : base + n < UInt256.size
  · exact congrArg UInt256.toNat (usub_uadd_lit_cancel hbase hn hadd)
  · have hsum_ge : UInt256.size ≤ base + n := by omega
    have hsum_lt2 : base + n < 2 * UInt256.size := by omega
    have hmod : (base + n) % UInt256.size = base + n - UInt256.size := by
      rw [Nat.mod_eq_sub_mod hsum_ge]
      exact Nat.mod_eq_of_lt (by omega)
    have haddn :
        (UInt256.add (UInt256.ofNat base) (UInt256.ofNat n)).toNat =
          base + n - UInt256.size := by
      rw [show UInt256.add (UInt256.ofNat base) (UInt256.ofNat n)
            = UInt256.ofNat base + UInt256.ofNat n from rfl,
          uadd_toNat, ulit_toNat' base hbase, ulit_toNat' n hn, hmod]
    change (UInt256.sub (UInt256.add (UInt256.ofNat base) (UInt256.ofNat n))
        (UInt256.ofNat base)).toNat = (UInt256.ofNat n).toNat
    rw [usub_toNat_underflow (a := UInt256.add (UInt256.ofNat base) (UInt256.ofNat n))
        (b := UInt256.ofNat base) (by rw [haddn, ulit_toNat' base hbase]; omega),
        haddn, ulit_toNat' base hbase, ulit_toNat' n hn]
    omega

/-! ## Unsigned comparisons and small arithmetic helpers -/

/-! ### Arithmetic and bitwise normalization -/

theorem nat_land_comm (a b : ℕ) : Nat.land a b = Nat.land b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a &&& b).testBit i = (b &&& a).testBit i
  rw [Nat.testBit_and, Nat.testBit_and, Bool.and_comm]

/-- Bitwise `AND` is bounded by its right operand. -/
theorem nat_land_le_right (a b : ℕ) : Nat.land a b ≤ b := by
  refine Nat.le_of_testBit fun i hi => ?_
  change (a &&& b).testBit i = true at hi
  rw [Nat.testBit_and] at hi
  simp only [Bool.and_eq_true] at hi
  exact hi.2

theorem u256_land_comm (a b : UInt256) : UInt256.land a b = UInt256.land b a := by
  apply u256_inj
  show Nat.land a.toNat b.toNat % UInt256.size =
    Nat.land b.toNat a.toNat % UInt256.size
  rw [nat_land_comm]

theorem nat_lor_comm (a b : ℕ) : Nat.lor a b = Nat.lor b a := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (a ||| b).testBit i = (b ||| a).testBit i
  rw [Nat.testBit_or, Nat.testBit_or, Bool.or_comm]

/-- Appending high bits above a bounded low field is ordinary addition. -/
theorem nat_lor_shift_add (a b k : Nat) (ha : a < 2 ^ k) :
    Nat.lor a (b * 2 ^ k) = a + b * 2 ^ k := by
  induction k generalizing a b with
  | zero =>
      have ha0 : a = 0 := by omega
      subst a
      norm_num
      change (0 ||| b) = b
      simp
  | succ k ih =>
      have hdiv : Nat.div2 a < 2 ^ k := by
        rw [Nat.div2_val]
        apply Nat.div_lt_of_lt_mul
        rw [show 2 * 2 ^ k = 2 ^ (k + 1) by ring_nf]
        exact ha
      nth_rewrite 1 [← Nat.bit_bodd_div2 a]
      rw [show b * 2 ^ (k + 1) = Nat.bit false (b * 2 ^ k) by
        rw [Nat.bit_val, Bool.toNat_false, Nat.pow_succ]
        ring]
      change (Nat.bit (Nat.bodd a) (Nat.div2 a) ||| Nat.bit false (b * 2 ^ k)) =
        a + Nat.bit false (b * 2 ^ k)
      rw [Nat.lor_bit]
      rw [Bool.or_false]
      change Nat.bit (Nat.bodd a) (Nat.lor (Nat.div2 a) (b * 2 ^ k)) =
        a + Nat.bit false (b * 2 ^ k)
      rw [ih (Nat.div2 a) b hdiv]
      rw [Nat.bit_val, Nat.bit_val, Bool.toNat_false]
      have hdecomp : (Nat.bodd a).toNat + Nat.div2 a * 2 = a := by
        simpa [Nat.mul_comm] using Nat.bodd_add_div2 a
      omega

theorem u256_lor_comm (a b : UInt256) : UInt256.lor a b = UInt256.lor b a := by
  apply u256_inj
  show Nat.lor a.toNat b.toNat % UInt256.size =
    Nat.lor b.toNat a.toNat % UInt256.size
  rw [nat_lor_comm]

theorem u256_lor_zero (a : UInt256) : UInt256.lor a ⟨0⟩ = a := by
  apply u256_inj
  change Nat.lor a.toNat 0 % UInt256.size = a.toNat
  have hlor : Nat.lor a.toNat 0 = a.toNat := by
    refine Nat.eq_of_testBit_eq fun i => ?_
    change Nat.testBit (a.toNat ||| 0) i = Nat.testBit a.toNat i
    rw [Nat.testBit_or]
    simp
  rw [hlor]
  exact Nat.mod_eq_of_lt a.val.isLt

theorem u256_add_comm (a b : UInt256) : a + b = b + a := by
  apply u256_inj
  rw [uadd_toNat, uadd_toNat, Nat.add_comm]

theorem u256_add_assoc (a b c : UInt256) : (a + b) + c = a + (b + c) := by
  apply u256_inj
  simp [uadd_toNat, Nat.add_assoc]

theorem u256_zero_add (a : UInt256) : (⟨0⟩ : UInt256) + a = a := by
  apply u256_inj
  show (0 + a.val).val = a.val
  simp

theorem u256_mul_comm (a b : UInt256) : UInt256.mul a b = UInt256.mul b a := by
  apply u256_inj
  show (a.val * b.val).val = (b.val * a.val).val
  rw [Fin.val_mul, Fin.val_mul, Nat.mul_comm]

theorem u256_lor_toNat (a b : UInt256) :
    (UInt256.lor a b).toNat = Nat.lor a.toNat b.toNat % UInt256.size := rfl

theorem u256_land_toNat (a b : UInt256) :
    (UInt256.land a b).toNat = Nat.land a.toNat b.toNat % UInt256.size := rfl

theorem uInt256_land_one_toNat (a : UInt256) :
    (UInt256.land a ⟨1⟩).toNat = a.toNat % 2 := by
  rw [u256_land_toNat]
  change Nat.land a.toNat 1 % UInt256.size = a.toNat % 2
  rw [show Nat.land a.toNat 1 = a.toNat % 2 by
    rw [nat_land_comm]
    exact Nat.one_and_eq_mod_two a.toNat]
  exact Nat.mod_eq_of_lt (by
    have hlt : a.toNat % 2 < 2 := Nat.mod_lt _ (by decide)
    norm_num [UInt256.size]
    omega)

theorem udiv_toNat (a b : UInt256) :
    (UInt256.div a b).toNat = a.toNat / b.toNat := by
  show (a.val / b.val).val = a.toNat / b.toNat
  rfl

theorem u256_mul_toNat (a b : UInt256) :
    (UInt256.mul a b).toNat = a.toNat * b.toNat % UInt256.size := by
  show (a.val * b.val).val = a.toNat * b.toNat % UInt256.size
  rw [Fin.val_mul]
  rfl

/-- General `HMul.hMul` `toNat` (mod `size`). -/
theorem u256_mul_op_toNat (a b : UInt256) :
    (a * b).toNat = a.toNat * b.toNat % UInt256.size := by
  show (a.val * b.val).val = a.toNat * b.toNat % UInt256.size
  rw [Fin.val_mul]
  rfl

theorem umul_toNat (a b : UInt256) (h : a.toNat * b.toNat < UInt256.size) :
    (a * b).toNat = a.toNat * b.toNat := by
  rw [u256_mul_op_toNat, Nat.mod_eq_of_lt h]

/-- Multiplication by two agrees with rebuilding the wrapped natural product. -/
theorem u256_mul_two_ofNat (a : UInt256) :
    UInt256.mul a ⟨2⟩ = UInt256.ofNat (a.toNat * 2) := by
  apply u256_inj
  show (a.val * (⟨2⟩ : UInt256).val).val = (Fin.ofNat UInt256.size (a.toNat * 2)).val
  rw [Fin.val_mul]
  rfl

/-- Bit access for a natural left shift, phrased to avoid expanding shift internals at call sites. -/
theorem testBit_shiftLeft (m k i : Nat) :
    (m <<< k).testBit i = if i < k then false else m.testBit (i - k) := by
  induction k generalizing i with
  | zero => simp
  | succ k ih =>
      rw [← Nat.shiftLeft'_false (m := m) (n := k + 1)]
      change (Nat.bit false (Nat.shiftLeft' false m k)).testBit i = _
      cases i with
      | zero => simp
      | succ i =>
          rw [Nat.testBit_bit_succ]
          rw [Nat.shiftLeft'_false]
          rw [ih]
          by_cases hi : i + 1 < k + 1
          · have hik : i < k := by omega
            simp [hi, hik]
          · have hnk : ¬ i < k := by omega
            simp [hi, hnk, Nat.succ_sub_succ_eq_sub]

theorem nat_testBit_shiftLeft (m k i : Nat) :
    (m <<< k).testBit i = if i < k then false else m.testBit (i - k) :=
  testBit_shiftLeft m k i

/-- Bit access after dropping the low `k` bits by division. -/
theorem divPow_testBit (n k i : Nat) (hk : k ≤ i) :
    (n / 2 ^ k).testBit (i - k) = n.testBit i := by
  simp [Nat.testBit, Nat.shiftRight_eq_div_pow]
  rw [Nat.div_div_eq_div_mul]
  rw [show 2 ^ k * 2 ^ (i - k) = 2 ^ i by
    rw [← Nat.pow_add]
    congr
    omega]

theorem nat_div_pow_testBit (n k i : Nat) (hk : k ≤ i) :
    (n / 2 ^ k).testBit (i - k) = n.testBit i :=
  divPow_testBit n k i hk

theorem nat_land_mask_eq_mod (n k : Nat) :
    Nat.land n (2 ^ k - 1) = n % 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  show (n &&& (2 ^ k - 1)).testBit i = (n % 2 ^ k).testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
  by_cases hi : i < k
  · rw [decide_eq_true hi]
    simp
  · rw [decide_eq_false hi]
    simp

/-- Clearing the low `k` bits of a 256-bit natural leaves the high field shifted back in place. -/
theorem natLandClearLow (n k : Nat) (hk : k ≤ 256) (hn : n < 2 ^ 256) :
    Nat.land n ((2 : Nat) ^ 256 - 2 ^ k) = (n / 2 ^ k) * 2 ^ k := by
  apply Nat.eq_of_testBit_eq
  intro i
  change (n &&& ((2 : Nat) ^ 256 - 2 ^ k)).testBit i =
    ((n / 2 ^ k) * 2 ^ k).testBit i
  rw [Nat.testBit_and]
  rw [show (2 : Nat) ^ 256 - 2 ^ k = (2 ^ (256 - k) - 1) <<< k by
    rw [Nat.shiftLeft_eq]
    rw [Nat.sub_mul]
    rw [one_mul]
    rw [show 2 ^ (256 - k) * 2 ^ k = (2 : Nat) ^ 256 by
      rw [← Nat.pow_add]
      congr
      omega]]
  rw [testBit_shiftLeft]
  rw [show (n / 2 ^ k) * 2 ^ k = (n / 2 ^ k) <<< k by rw [Nat.shiftLeft_eq]]
  rw [testBit_shiftLeft]
  by_cases hik : i < k
  · simp [hik]
  · simp [hik]
    have hki : k ≤ i := Nat.le_of_not_gt hik
    by_cases hi256 : i < 256
    · have hlt : i - k < 256 - k := by omega
      simp [hlt]
      exact (divPow_testBit n k i hki).symm
    · have hnlt : ¬ i - k < 256 - k := by omega
      simp [hnlt]
      change (n / 2 ^ k).testBit (i - k) = false
      have hq : n / 2 ^ k < 2 ^ (256 - k) := by
        apply Nat.div_lt_of_lt_mul
        rw [show 2 ^ k * 2 ^ (256 - k) = (2 : Nat) ^ 256 by
          rw [← Nat.pow_add]
          congr
          omega]
        exact hn
      have hpow : n / 2 ^ k < 2 ^ (i - k) := by
        exact lt_of_lt_of_le hq (Nat.pow_le_pow_right (by norm_num) (by omega))
      exact Nat.testBit_lt_two_pow hpow

theorem u256_land_high_mask_eq_self (w : UInt256) {k : Nat} (hk : k ≤ 256)
    (hlow : w.toNat % 2 ^ k = 0) :
    UInt256.land w (UInt256.ofNat ((2 : Nat) ^ 256 - 2 ^ k)) = w := by
  apply u256_inj
  rw [u256_land_toNat]
  have hmaskLt : (2 : Nat) ^ 256 - 2 ^ k < UInt256.size := by
    have hpowPos : 0 < (2 : Nat) ^ k := by positivity
    change (2 : Nat) ^ 256 - 2 ^ k < 2 ^ 256
    omega
  rw [ulit_toNat' _ hmaskLt]
  rw [natLandClearLow w.toNat k hk w.val.isLt]
  have hdiv : w.toNat / 2 ^ k * 2 ^ k = w.toNat := by
    have h := Nat.div_add_mod w.toNat (2 ^ k)
    rw [hlow, add_zero] at h
    rw [Nat.mul_comm] at h
    exact h
  rw [hdiv]
  exact Nat.mod_eq_of_lt w.val.isLt

/-- `LT` returns `1` when the strict order holds. -/
theorem ult_one {a b : UInt256} (h : a.toNat < b.toNat) : UInt256.lt a b = ⟨1⟩ := by
  show UInt256.fromBool (decide (a < b)) = ⟨1⟩
  rw [decide_eq_true (show a < b from h)]
  rfl

/-- `LT` returns `0` when the strict order fails. -/
theorem ult_zero {a b : UInt256} (h : b.toNat ≤ a.toNat) : UInt256.lt a b = ⟨0⟩ := by
  show UInt256.fromBool (decide (a < b)) = ⟨0⟩
  rw [decide_eq_false (show ¬ (a < b) from by show ¬ (a.toNat < b.toNat); omega)]
  rfl

/-- `GT` returns `1` when the strict order holds. -/
theorem ugt_one {a b : UInt256} (h : b.toNat < a.toNat) : UInt256.gt a b = ⟨1⟩ := by
  show UInt256.fromBool (decide (a > b)) = ⟨1⟩
  rw [decide_eq_true (show a > b from h)]
  rfl

/-- `GT` returns `0` when the strict order fails. -/
theorem ugt_zero {a b : UInt256} (h : a.toNat ≤ b.toNat) : UInt256.gt a b = ⟨0⟩ := by
  show UInt256.fromBool (decide (a > b)) = ⟨0⟩
  rw [decide_eq_false (show ¬ (a > b) from by show ¬ (a.toNat > b.toNat); omega)]
  rfl

/-- `2^m` stays below `2^256 = UInt256.size` for `m < 256`. -/
theorem pow_lt_size {m : ℕ} (h : m < 256) : (2:ℕ) ^ m < UInt256.size := by
  have : (2:ℕ)^m < 2^256 := Nat.pow_lt_pow_right (by norm_num) h
  simpa [UInt256.size] using this

/-- `(ofNat (2^m)).toNat = 2^m` when `2^m` is in range. -/
theorem ofNat_pow_toNat {m : ℕ} (h : m < 256) : (UInt256.ofNat (2 ^ m)).toNat = 2 ^ m := by
  show (Fin.ofNat _ (2^m)).val = 2 ^ m
  simp only [Fin.ofNat]
  exact Nat.mod_eq_of_lt (pow_lt_size h)

/-- Any `m < 256` fits in `UInt256`. -/
theorem lt_size_of_lt256 {m : ℕ} (h : m < 256) : m < UInt256.size := by
  have : (256:ℕ) ≤ UInt256.size := by
    have : (2:ℕ)^8 ≤ 2^256 := Nat.pow_le_pow_right (by norm_num) (by norm_num)
    simp [UInt256.size]
  omega

/-- `r * 2` does not wrap when `2 * r.toNat` is in range. -/
theorem mul2_toNat {r : UInt256} (h : 2 * r.toNat < UInt256.size) :
    (UInt256.mul r ⟨2⟩).toNat = 2 * r.toNat := by
  show (r.val * (⟨2⟩ : UInt256).val).val = 2 * r.toNat
  rw [Fin.val_mul]
  show (r.toNat * 2) % UInt256.size = 2 * r.toNat
  rw [Nat.mul_comm]
  exact Nat.mod_eq_of_lt h

/-- `i + 1` does not wrap when `i.toNat + 1` is in range. -/
theorem add1_toNat {i : UInt256} (h : i.toNat + 1 < UInt256.size) :
    (i + ⟨1⟩).toNat = i.toNat + 1 := by
  show (i.val + (⟨1⟩ : UInt256).val).val = i.toNat + 1
  rw [Fin.val_add]
  show (i.toNat + 1) % UInt256.size = i.toNat + 1
  exact Nat.mod_eq_of_lt h

/-- Addition of three in-range naturals does not wrap. -/
theorem uadd3_ofNat_toNat {a b c : Nat}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hc : c < UInt256.size)
    (hab : a + b < UInt256.size) (habc : a + b + c < UInt256.size) :
    ((UInt256.ofNat a + UInt256.ofNat b) + UInt256.ofNat c).toNat = a + b + c := by
  rw [uadd_toNat]
  have habWord : (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b :=
    uadd_ofNat_toNat ha hb hab
  rw [habWord, ulit_toNat' c hc]
  exact Nat.mod_eq_of_lt habc

theorem u256_one_add_ofNat (i : Nat) :
    (⟨1⟩ : UInt256) + UInt256.ofNat i = UInt256.ofNat (i + 1) := by
  apply u256_inj
  rw [uadd_toNat]
  show ((⟨1⟩ : UInt256).toNat + (UInt256.ofNat i).toNat) % UInt256.size =
    (UInt256.ofNat (i + 1)).toNat
  simp only [UInt256.toNat]
  change (1 + (Fin.ofNat UInt256.size i).val) % UInt256.size =
    (Fin.ofNat UInt256.size (i + 1)).val
  rw [Fin.val_ofNat, Fin.val_ofNat]
  rw [Nat.add_mod]
  simp [Nat.add_comm]

/-- `SHL 5` of a non-wrapping natural word is multiplication by 32. -/
theorem shiftLeft5_ofNat_eq {n : Nat} (h : 32 * n < UInt256.size) :
    UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩ = UInt256.ofNat (32 * n) := by
  apply u256_inj
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨5⟩ : UInt256).val ≥ 256))]
  change (((UInt256.ofNat n).val.val <<< (⟨5⟩ : UInt256).val.val) % UInt256.size) =
    (UInt256.ofNat (32 * n)).val.val
  rw [show (⟨5⟩ : UInt256).val.val = 5 by decide]
  rw [show (UInt256.ofNat n).val.val = n by
    exact ulit_toNat' n (by
      have : n ≤ 32 * n := by omega
      exact lt_of_le_of_lt this h)]
  rw [show (UInt256.ofNat (32 * n)).val.val = 32 * n by exact ulit_toNat' (32 * n) h]
  rw [Nat.shiftLeft_eq, Nat.mul_comm]
  exact Nat.mod_eq_of_lt h

/-! ## Signed `SLT` over EVM words -/

/-- `GT` is boolean-valued, so if it is not `1` then it is `0`. -/
theorem ugt_eq_zero_of_ne_one {a b : UInt256}
    (h : ¬ UInt256.gt a b = ⟨1⟩) : UInt256.gt a b = ⟨0⟩ := by
  by_cases hab : a > b
  · exact False.elim (h (by
      simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, hab]
      decide))
  · simp [UInt256.gt, UInt256.fromBool, Bool.toUInt256, hab]
    decide

/-- `SLT` of a non-negative word against a negative word is zero. -/
theorem slt_zero_low_high {a b : UInt256}
    (ha : a.toNat < 2 ^ 255) (hb : 2 ^ 255 ≤ b.toNat) :
    UInt256.slt a b = ⟨0⟩ := by
  unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
  rw [if_neg (by omega : ¬ a.toNat ≥ 2 ^ 255), if_pos hb]
  rfl

/-- `SLT` is boolean-valued, so if it is not `1` then it is `0`. -/
theorem uslt_eq_zero_of_ne_one {a b : UInt256}
    (h : ¬ UInt256.slt a b = ⟨1⟩) : UInt256.slt a b = ⟨0⟩ := by
  unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
  by_cases ha : a.toNat ≥ 2 ^ 255
  · rw [if_pos ha]
    by_cases hb : b.toNat ≥ 2 ^ 255
    · rw [if_pos hb]
      by_cases hab : a < b
      · exfalso
        apply h
        unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
        rw [if_pos ha, if_pos hb, if_pos (decide_eq_true hab)]
        native_decide
      · have hdf : ¬ decide (a < b) = true := by
          rw [decide_eq_false hab]
          decide
        rw [if_neg hdf]
        native_decide
    · rw [if_neg hb]
      exfalso
      apply h
      unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
      rw [if_pos ha, if_neg hb]
      native_decide
  · rw [if_neg ha]
    by_cases hb : b.toNat ≥ 2 ^ 255
    · rw [if_pos hb]
      native_decide
    · rw [if_neg hb]
      by_cases hab : a < b
      · exfalso
        apply h
        unfold UInt256.slt UInt256.sltBool UInt256.fromBool Bool.toUInt256
        rw [if_neg ha, if_neg hb, if_pos (decide_eq_true hab)]
        native_decide
      · have hdf : ¬ decide (a < b) = true := by
          rw [decide_eq_false hab]
          decide
        rw [if_neg hdf]
        native_decide

/-- `SLT a m = 0` when both words are non-negative and `a ≥ m`. -/
theorem slt_lit_zero {a : UInt256} {m : ℕ}
    (hm : m < 2 ^ 255) (hlo : m ≤ a.toNat) (hhi : a.toNat < 2 ^ 255) :
    UInt256.slt a (UInt256.ofNat m) = ⟨0⟩ := by
  have hmNat : (UInt256.ofNat m).toNat = m := ulit_toNat' m (lt_size_of_lt_sign hm)
  have hbool : UInt256.sltBool a (UInt256.ofNat m) = false := by
    unfold UInt256.sltBool
    rw [if_neg (show ¬ a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (UInt256.ofNat m).toNat ≥ 2 ^ 255 by rw [hmNat]; omega)]
    exact decide_eq_false (show ¬ a < UInt256.ofNat m by
      show ¬ a.toNat < (UInt256.ofNat m).toNat
      rw [hmNat]
      omega)
  show UInt256.fromBool (UInt256.sltBool a (UInt256.ofNat m)) = ⟨0⟩
  rw [hbool]
  rfl

/-- `SLT a m = 1` when both words are non-negative and `a < m`. -/
theorem slt_lit_one_low {a : UInt256} {m : ℕ}
    (hm : m < 2 ^ 255) (hlo : a.toNat < m) :
    UInt256.slt a (UInt256.ofNat m) = ⟨1⟩ := by
  have hmNat : (UInt256.ofNat m).toNat = m := ulit_toNat' m (lt_size_of_lt_sign hm)
  have hbool : UInt256.sltBool a (UInt256.ofNat m) = true := by
    unfold UInt256.sltBool
    rw [if_neg (show ¬ a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (UInt256.ofNat m).toNat ≥ 2 ^ 255 by rw [hmNat]; omega)]
    exact decide_eq_true (show a < UInt256.ofNat m by
      show a.toNat < (UInt256.ofNat m).toNat
      rw [hmNat]
      omega)
  show UInt256.fromBool (UInt256.sltBool a (UInt256.ofNat m)) = ⟨1⟩
  rw [hbool]
  rfl

/-- `SGT a m = 1` when both words are non-negative and `a > m`. -/
theorem sgt_lit_one {a : UInt256} {m : ℕ}
    (hm : m < 2 ^ 255) (hlo : m < a.toNat) (hhi : a.toNat < 2 ^ 255) :
    UInt256.sgt a (UInt256.ofNat m) = ⟨1⟩ := by
  have hmNat : (UInt256.ofNat m).toNat = m := ulit_toNat' m (lt_size_of_lt_sign hm)
  have hbool : UInt256.sgtBool a (UInt256.ofNat m) = true := by
    unfold UInt256.sgtBool
    rw [if_neg (show ¬ a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (UInt256.ofNat m).toNat ≥ 2 ^ 255 by rw [hmNat]; omega)]
    exact decide_eq_true (show a > UInt256.ofNat m by
      show (UInt256.ofNat m).toNat < a.toNat
      rw [hmNat]
      omega)
  show UInt256.fromBool (UInt256.sgtBool a (UInt256.ofNat m)) = ⟨1⟩
  rw [hbool]
  rfl

/-- `SLT a m = 1` when `a` has the sign bit set and `m` is non-negative. -/
theorem slt_lit_one_high {a : UInt256} {m : ℕ}
    (hm : m < 2 ^ 255) (hhi : 2 ^ 255 ≤ a.toNat) :
    UInt256.slt a (UInt256.ofNat m) = ⟨1⟩ := by
  have hmNat : (UInt256.ofNat m).toNat = m := ulit_toNat' m (lt_size_of_lt_sign hm)
  have hbool : UInt256.sltBool a (UInt256.ofNat m) = true := by
    unfold UInt256.sltBool
    rw [if_pos (show a.toNat ≥ 2 ^ 255 by omega),
        if_neg (show ¬ (UInt256.ofNat m).toNat ≥ 2 ^ 255 by rw [hmNat]; omega)]
  show UInt256.fromBool (UInt256.sltBool a (UInt256.ofNat m)) = ⟨1⟩
  rw [hbool]
  rfl

/-- `SLT (ofNat n) m = 0` for non-negative, non-wrapping naturals with `n ≥ m`. -/
theorem slt_ofNat_lit_zero {n m : ℕ}
    (hm : m < 2 ^ 255) (hlo : m ≤ n) (hhi : n < 2 ^ 255) :
    UInt256.slt (UInt256.ofNat n) (UInt256.ofNat m) = ⟨0⟩ := by
  apply slt_lit_zero hm
  · rw [ulit_toNat' n (lt_size_of_lt_sign hhi)]
    exact hlo
  · rw [ulit_toNat' n (lt_size_of_lt_sign hhi)]
    exact hhi

/-- `SLT (ofNat n) m = 1` for non-negative, non-wrapping naturals with `n < m`. -/
theorem slt_ofNat_lit_one_low {n m : ℕ}
    (hm : m < 2 ^ 255) (hlo : n < m) :
    UInt256.slt (UInt256.ofNat n) (UInt256.ofNat m) = ⟨1⟩ := by
  apply slt_lit_one_low hm
  rw [ulit_toNat' n (lt_size_of_lt_sign (lt_trans hlo hm))]
  exact hlo

/-! ## Small arithmetic tactic

`evm_arith` is deliberately modest: it handles closed literal goals immediately, and can close many
side conditions after a parametric word lemma has reduced them to natural arithmetic.  It is not
intended to replace the named lemmas above.
-/

macro "evm_arith" : tactic =>
  `(tactic|
    first
    | decide
    | omega
    | norm_num [UInt256.size]
    | (simp only [UInt256.size] <;> omega))

/-! ## Word equality (`UInt256.eq`) and low-bit masking -/

/-- The EVM `EQ` of a word with itself is `1`. -/
theorem uInt256_eq_self (a : UInt256) : UInt256.eq a a = ⟨1⟩ := by
  have h : UInt256.eq a a = UInt256.ofNat 1 := by simp [UInt256.eq, UInt256.fromBool]
  rw [h]; rfl

/-- The EVM `EQ` of two words that do not compare equal to `1` is `0`. -/
theorem uInt256_eq_zero_of_ne {a b : UInt256} (h : ¬ UInt256.eq a b = ⟨1⟩) :
    UInt256.eq a b = ⟨0⟩ := by
  by_cases hab : a = b
  · subst hab; exact absurd (uInt256_eq_self a) h
  · show UInt256.fromBool (decide (a = b)) = ⟨0⟩
    rw [decide_eq_false hab]; rfl

/-- `EQ` returning `1` reflects word equality. -/
theorem uInt256_eq_one_eq {a b : UInt256} (h : UInt256.eq a b = ⟨1⟩) : a = b := by
  by_contra hne
  simp only [UInt256.eq, UInt256.fromBool, Bool.toUInt256, hne, decide_false,
    Bool.false_eq_true, ↓reduceIte] at h
  exact absurd h (by decide)

/-- EVM word equality is symmetric. -/
theorem uInt256_eq_comm (a b : UInt256) : UInt256.eq a b = UInt256.eq b a := by
  by_cases h : a = b
  · subst b
    rfl
  · have hba : b ≠ a := by
      intro hb
      exact h hb.symm
    simp [UInt256.eq, UInt256.fromBool, h, hba]

/-- `AND` with the low-160-bit mask is the identity on values below `2^160`. -/
theorem land_mask160 (n : ℕ) (h : n < 2 ^ 160) : Nat.land n (2 ^ 160 - 1) = n := by
  apply Nat.eq_of_testBit_eq; intro i
  show (n &&& (2 ^ 160 - 1)).testBit i = n.testBit i
  rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < 160
  · rw [decide_eq_true hi, Bool.and_true]
  · rw [decide_eq_false hi, Bool.and_false]
    have : n < 2 ^ i := lt_of_lt_of_le h (Nat.pow_le_pow_right (by norm_num) (by omega))
    exact (Nat.testBit_lt_two_pow this).symm

/-! ## `UInt256` order — `compare` reduces to the wrapped `Fin`, and the resulting `Std.*Cmp`
instances (used to drive `Batteries.RBMap` storage-map lemmas). -/

/-- The derived `UInt256` order compares the wrapped `Fin` values. -/
@[simp] theorem uInt256_compare_eq_val_compare (a b : UInt256) :
    compare a b = compare a.val b.val := by
  cases a
  cases b
  simp [compare, Ethereum.instOrdUInt256.ord]

instance : Std.OrientedCmp (compare : UInt256 → UInt256 → Ordering) where
  eq_swap := by
    intro a b
    rw [uInt256_compare_eq_val_compare a b, uInt256_compare_eq_val_compare b a]
    exact Std.OrientedCmp.eq_swap

instance : Std.TransCmp (compare : UInt256 → UInt256 → Ordering) where
  isLE_trans := by
    intro a b c hab hbc
    rw [uInt256_compare_eq_val_compare a b] at hab
    rw [uInt256_compare_eq_val_compare b c] at hbc
    rw [uInt256_compare_eq_val_compare a c]
    exact Std.TransCmp.isLE_trans hab hbc

instance : Std.ReflCmp (compare : UInt256 → UInt256 → Ordering) where
  compare_self := by
    intro a
    rw [uInt256_compare_eq_val_compare a a]
    exact Std.ReflCmp.compare_self

instance : Std.LawfulEqCmp (compare : UInt256 → UInt256 → Ordering) where
  eq_of_compare := by
    intro a b h
    rw [uInt256_compare_eq_val_compare a b] at h
    have hv : a.val = b.val := Std.LawfulEqCmp.eq_of_compare h
    cases a
    cases b
    cases hv
    rfl

/-! ## Bitwise word-rounding (solc memory allocation)

solc rounds an allocation size up to the next 32-byte word with `(size + 0x3f) & ~0x1f`.  These
lemmas evaluate that rounding for a size that is already a multiple of 32 (the dynamic-array data
length `0x20 * n`), giving the clean `size + 0x20`. -/

/-- Big-endian `Nat`-level mask: anding off the low 5 bits floors to a multiple of 32.  Proved by
    `(2^256 - 32) = (2^251 - 1) * 2^5` and bit extensionality. -/
theorem nat_land_mask (m : ℕ) (h : m < 2 ^ 256) : m &&& (2 ^ 256 - 32) = 32 * (m / 32) := by
  have hmask : (2:ℕ) ^ 256 - 32 = (2 ^ 251 - 1) * 2 ^ 5 := by norm_num
  apply Nat.eq_of_testBit_eq
  intro i
  rw [hmask, Nat.testBit_and, Nat.testBit_mul_two_pow, Nat.testBit_two_pow_sub_one,
    show 32 * (m / 32) = (m >>> 5) * 2 ^ 5 by rw [Nat.shiftRight_eq_div_pow]; ring,
    Nat.testBit_mul_two_pow, Nat.testBit_shiftRight]
  by_cases hi : 5 ≤ i
  · simp only [hi, decide_true, Bool.true_and]
    by_cases hi256 : i - 5 < 251
    · simp only [hi256, decide_true, Bool.and_true]
      rw [show 5 + (i - 5) = i by omega]
    · simp only [hi256, decide_false, Bool.and_false]
      have hb : m.testBit i = false := Nat.testBit_lt_two_pow (lt_of_lt_of_le h
        (Nat.pow_le_pow_right (by norm_num) (by omega : (256:ℕ) ≤ i)))
      rw [show 5 + (i - 5) = i by omega, hb]
  · simp only [hi, decide_false, Bool.false_and, Bool.and_false]

/-- `UInt256.land` is `Nat`-level `&&&` on `toNat` (the mask never grows past either operand). -/
theorem uland_toNat (a b : UInt256) : (UInt256.land a b).toNat = a.toNat &&& b.toNat := by
  unfold UInt256.land UInt256.toNat Fin.land
  simp only []
  exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.and_le_left) a.val.isLt)

/-- `~0x1f` as a 256-bit word is `2^256 - 32`. -/
theorem lnot31_toNat : (UInt256.lnot ⟨31⟩).toNat = 2 ^ 256 - 32 := by unfold UInt256.lnot; decide

/-- The solc allocation word-rounding: `(x + 0x3f) &&& ~0x1f = x + 0x20` when `x` is a multiple of
    32 (here `x = 0x20 * length` is the dynamic-array data byte-size). -/
theorem alloc_round (x : UInt256) (n : ℕ) (hx : x.toNat = 32 * n) (hxb : x.toNat + 63 < 2 ^ 256) :
    UInt256.land (UInt256.lnot ⟨31⟩) (x + ⟨63⟩) = x + ⟨32⟩ := by
  apply u256_inj
  have h63 : ((⟨63⟩ : UInt256)).toNat = 63 := by decide
  have h32 : ((⟨32⟩ : UInt256)).toNat = 32 := by decide
  have hsz : UInt256.size = 2 ^ 256 := by decide
  rw [uland_toNat, lnot31_toNat, uadd_toNat, uadd_toNat, h63, h32, hsz,
      Nat.mod_eq_of_lt (by omega : x.toNat + 63 < 2 ^ 256),
      Nat.mod_eq_of_lt (by omega : x.toNat + 32 < 2 ^ 256),
      Nat.and_comm, nat_land_mask _ (by omega)]
  omega

/-- `SHL` by 5 of a length literal is multiplication by 32 (no wrap for `n < 2^251`).  solc uses
    `n << 5` to turn an element count into the `0x20 * n` data byte-size. -/
theorem ushl5_ofNat_toNat (n : ℕ) (hn : n < 2 ^ 251) :
    (UInt256.shiftLeft (UInt256.ofNat n) ⟨5⟩).toNat = 32 * n := by
  have hofn : ((UInt256.ofNat n) : UInt256).toNat = n := ulit_toNat' n (lt_trans hn (by decide))
  unfold UInt256.shiftLeft
  rw [if_neg (by decide : ¬ ((⟨5⟩ : UInt256).val ≥ 256))]
  show (Fin.shiftLeft (UInt256.ofNat n).val (⟨5⟩ : UInt256).val).val = 32 * n
  unfold Fin.shiftLeft
  show ((UInt256.ofNat n).toNat <<< (5 : ℕ)) % UInt256.size = 32 * n
  rw [hofn, Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by
    have hub : (2:ℕ) ^ 251 * 2 ^ 5 ≤ UInt256.size := by decide
    calc n * 2 ^ 5 < 2 ^ 251 * 2 ^ 5 := Nat.mul_lt_mul_of_pos_right hn (by norm_num)
      _ ≤ UInt256.size := hub)]
  ring

end Reasoning.Theory
