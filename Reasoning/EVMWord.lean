import Reasoning.Theory

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

/-- General `ADD` `toNat` (mod `size`). -/
theorem uadd_toNat (a b : UInt256) : (a + b).toNat = (a.toNat + b.toNat) % UInt256.size := by
  show (a.val + b.val).val = (a.val.val + b.val.val) % UInt256.size
  rw [Fin.add_def]

theorem u256_add_comm (a b : UInt256) : a + b = b + a := by
  apply u256_inj
  rw [uadd_toNat, uadd_toNat, Nat.add_comm]

theorem u256_one_add_ofNat (n : ℕ) : (⟨1⟩ : UInt256) + UInt256.ofNat n =
    UInt256.ofNat (n + 1) := by
  apply u256_inj
  show ((⟨1⟩ : UInt256) + UInt256.ofNat n).toNat =
    (UInt256.ofNat (n + 1)).toNat
  rw [uadd_toNat]
  change (1 + (Fin.ofNat UInt256.size n).val) % UInt256.size =
    (Fin.ofNat UInt256.size (n + 1)).val
  rw [Fin.val_ofNat, Fin.val_ofNat]
  rw [Nat.add_comm 1 (n % UInt256.size)]
  have h1 : 1 % UInt256.size = 1 := by norm_num [UInt256.size]
  rw [← h1, ← Nat.add_mod]
  rw [h1]

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

/-- `ADD` of two in-range naturals does not wrap. -/
theorem uadd_ofNat_toNat {a b : ℕ}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hab : a + b < UInt256.size) :
    (UInt256.add (UInt256.ofNat a) (UInt256.ofNat b)).toNat = a + b := by
  rw [show UInt256.add (UInt256.ofNat a) (UInt256.ofNat b)
        = UInt256.ofNat a + UInt256.ofNat b from rfl,
      uadd_toNat, ulit_toNat' a ha, ulit_toNat' b hb, Nat.mod_eq_of_lt hab]

/-- `ADD` of three in-range naturals does not wrap. -/
theorem uadd3_ofNat_toNat {a b c : ℕ}
    (ha : a < UInt256.size) (hb : b < UInt256.size) (hc : c < UInt256.size)
    (hab : a + b < UInt256.size) (habc : a + b + c < UInt256.size) :
    ((UInt256.ofNat a + UInt256.ofNat b) + UInt256.ofNat c).toNat = a + b + c := by
  rw [uadd_toNat]
  have habWord : (UInt256.ofNat a + UInt256.ofNat b).toNat = a + b :=
    uadd_ofNat_toNat ha hb hab
  rw [habWord, ulit_toNat' c hc]
  exact Nat.mod_eq_of_lt habc

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

/-! ## Unsigned comparisons and small arithmetic helpers -/

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

/-- Low-bit masking by `1` is the same as reducing modulo `2`. -/
theorem nat_land_one_eq_mod_two (n : ℕ) :
    Nat.land n 1 = n % 2 := by
  have hmask : Nat.land n (2 ^ 1 - 1) = n % 2 ^ 1 := by
    apply Nat.eq_of_testBit_eq
    intro i
    show (n &&& (2 ^ 1 - 1)).testBit i = (n % 2 ^ 1).testBit i
    rw [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Nat.testBit_mod_two_pow]
    by_cases hi : i < 1
    · rw [decide_eq_true hi]
      simp
    · rw [decide_eq_false hi]
      simp
  simpa using hmask

/-- `UInt256.land w 1` exposes the same low bit as `w.toNat % 2`. -/
theorem uInt256_land_one_toNat (w : UInt256) :
    (UInt256.land w ⟨1⟩).toNat = w.toNat % 2 := by
  unfold UInt256.land UInt256.toNat
  cases w with
  | mk val =>
      cases val with
      | mk n hn =>
          have hlt : n % 2 < UInt256.size := by
            have h2 : n % 2 < 2 := Nat.mod_lt _ (by norm_num)
            norm_num [UInt256.size] at h2 ⊢
            omega
          change Nat.land n (1 % UInt256.size) % UInt256.size = n % 2
          rw [show 1 % UInt256.size = 1 from by norm_num [UInt256.size],
            nat_land_one_eq_mod_two, Nat.mod_eq_of_lt hlt]

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

theorem umul_toNat {a b : UInt256} (h : a.toNat * b.toNat < UInt256.size) :
    (a * b).toNat = a.toNat * b.toNat := by
  show (a.val * b.val).val = a.toNat * b.toNat
  rw [Fin.val_mul]
  exact Nat.mod_eq_of_lt h

theorem udiv_toNat (a b : UInt256) : (UInt256.div a b).toNat = a.toNat / b.toNat := by
  unfold UInt256.div UInt256.toNat
  rfl

theorem uadd_lit32_toNat {a : UInt256} (h : a.toNat + 32 < UInt256.size) :
    (((⟨32⟩ : UInt256) + a).toNat = a.toNat + 32) := by
  rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  rw [Nat.add_comm 32 a.toNat]
  exact Nat.mod_eq_of_lt h

theorem uadd_word_lit32_toNat {a : UInt256} (h : a.toNat + 32 < UInt256.size) :
    ((a + (⟨32⟩ : UInt256)).toNat = a.toNat + 32) := by
  rw [uadd_toNat, show (⟨32⟩ : UInt256).toNat = 32 from by decide]
  exact Nat.mod_eq_of_lt h

/-- `i + 1` does not wrap when `i.toNat + 1` is in range. -/
theorem add1_toNat {i : UInt256} (h : i.toNat + 1 < UInt256.size) :
    (i + ⟨1⟩).toNat = i.toNat + 1 := by
  show (i.val + (⟨1⟩ : UInt256).val).val = i.toNat + 1
  rw [Fin.val_add]
  show (i.toNat + 1) % UInt256.size = i.toNat + 1
  exact Nat.mod_eq_of_lt h

/-! ## Signed `SLT` over EVM words -/

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

/-- `SLT a b = 0` when `a` is non-negative and `b` has the sign bit set. -/
theorem slt_zero_of_left_low_right_high {a b : UInt256}
    (ha : a.toNat < 2 ^ 255) (hb : 2 ^ 255 ≤ b.toNat) :
    UInt256.slt a b = ⟨0⟩ := by
  have hbool : UInt256.sltBool a b = false := by
    unfold UInt256.sltBool
    rw [if_neg (show ¬ a.toNat ≥ 2 ^ 255 by omega), if_pos hb]
  show UInt256.fromBool (UInt256.sltBool a b) = ⟨0⟩
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

end Reasoning.Theory
