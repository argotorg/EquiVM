import Benchmarks.UniswapV4PoolManager.SignedWords

/-! Mathematical meaning of signed EVM comparisons and checked addition. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: connect signed Solidity normalization with the EVM interpretation.
theorem signed_eq_normalize (w : UInt256) :
    EVM.signed w = normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat w.toNat) := by
  rw [normalizeInt_sint256_word]
  rfl

-- LIBRARY CANDIDATE: SLT compares the mathematical signed interpretations.
theorem slt_signed (a b : UInt256) :
    UInt256.slt a b = UInt256.fromBool (decide (EVM.signed a < EVM.signed b)) := by
  have ha := a.val.isLt
  have hb := b.val.isLt
  change a.toNat < 2^256 at ha
  change b.toNat < 2^256 at hb
  unfold UInt256.slt UInt256.sltBool EVM.signed
  change UInt256.fromBool (if a.toNat ≥ 2^255 then
    if b.toNat ≥ 2^255 then decide (a.toNat < b.toNat) else true
    else if b.toNat ≥ 2^255 then false else decide (a.toNat < b.toNat)) =
    UInt256.fromBool (decide ((if a.toNat < 2^255 then (a.toNat : Int) else a.toNat - 2^256) <
      (if b.toNat < 2^255 then (b.toNat : Int) else b.toNat - 2^256)))
  congr 1
  split_ifs <;> simp_all <;> omega

-- LIBRARY CANDIDATE: the via-IR signed-add guard is exact, including both overflow directions.
theorem signedAddFits_iff (a b : UInt256) :
    int256Fits (EVM.signed a + EVM.signed b) ↔
      ((EVM.signed a < 0) ↔ (EVM.signed (a + b) < EVM.signed b)) := by
  have ha := a.val.isLt
  have hb := b.val.isLt
  change a.toNat < 2^256 at ha
  change b.toNat < 2^256 at hb
  change (-(2^255 : Int) ≤
      (if a.toNat < 2^255 then (a.toNat : Int) else a.toNat - 2^256) +
      (if b.toNat < 2^255 then (b.toNat : Int) else b.toNat - 2^256) ∧
      (if a.toNat < 2^255 then (a.toNat : Int) else a.toNat - 2^256) +
      (if b.toNat < 2^255 then (b.toNat : Int) else b.toNat - 2^256) < 2^255) ↔
    (((if a.toNat < 2^255 then (a.toNat : Int) else a.toNat - 2^256) < 0) ↔
      ((if (a + b).toNat < 2^255 then ((a + b).toNat : Int) else (a + b).toNat - 2^256) <
      (if b.toNat < 2^255 then (b.toNat : Int) else b.toNat - 2^256)))
  rw [uadd_toNat]
  change _ ↔ (_ ↔ ((if (a.toNat + b.toNat) % 2^256 < 2^255 then
    (((a.toNat + b.toNat) % 2^256 : Nat) : Int) else ((a.toNat + b.toNat) % 2^256 : Nat) - 2^256) < _))
  split_ifs <;> omega

-- LIBRARY CANDIDATE: a reusable form of the complete via-IR signed-add overflow expression.
theorem signedAddGuard (a b : UInt256) :
    UInt256.lor
      (UInt256.land (UInt256.isZero (UInt256.slt a ⟨0⟩)) (UInt256.slt (a + b) b))
      (UInt256.land (UInt256.slt a ⟨0⟩) (UInt256.isZero (UInt256.slt (a + b) b))) =
    UInt256.fromBool (decide (¬int256Fits (EVM.signed a + EVM.signed b))) := by
  rw [slt_signed, slt_signed]
  have hz : EVM.signed (⟨0⟩ : UInt256) = 0 := rfl
  rw [hz]
  have he := signedAddFits_iff a b
  by_cases ha : EVM.signed a < 0 <;>
    by_cases hs : EVM.signed (a + b) < EVM.signed b <;>
    simp only [ha, hs, decide_true, decide_false,
      iff_true, iff_false, not_true_eq_false] at he ⊢ <;>
    simp only [he] <;> decide

-- LIBRARY CANDIDATE: signed interpretation followed by encoding preserves a word.
theorem wordOfInt_signed (w : UInt256) : EVM.wordOfInt (EVM.signed w) = w := by
  apply u256_inj
  rw [wordOfInt_eq_mod]
  change ((EVM.signed w % (2^256 : Int)).toNat % 2^256) = w.toNat
  have hw := w.val.isLt
  change w.toNat < 2^256 at hw
  change (((if w.toNat < 2^255 then (w.toNat : Int) else w.toNat - 2^256) % (2^256 : Int)).toNat % 2^256) = _
  split_ifs <;> omega

-- LIBRARY CANDIDATE: signed addition encodes as modular word addition.
theorem wordOfInt_signed_add (a b : UInt256) :
    EVM.wordOfInt (EVM.signed a + EVM.signed b) = a + b := by
  apply u256_inj
  rw [wordOfInt_eq_mod, uadd_toNat]
  have ha := a.val.isLt
  have hb := b.val.isLt
  change a.toNat < 2^256 at ha
  change b.toNat < 2^256 at hb
  change (((if a.toNat < 2^255 then (a.toNat : Int) else a.toNat - 2^256) +
    (if b.toNat < 2^255 then (b.toNat : Int) else b.toNat - 2^256)) % (2^256 : Int)).toNat % 2^256 =
    (a.toNat + b.toNat) % 2^256
  split_ifs <;> omega

-- LIBRARY CANDIDATE: interpreting an encoded signed integer in range recovers that integer.
theorem signed_wordOfInt {i : Int} (hi : int256Fits i) : EVM.signed (EVM.wordOfInt i) = i := by
  symm
  apply int_eq_signed_word_of_range_mod hi.1 hi.2
  rw [wordOfInt_eq_mod]
  change i % (2^256 : Int) = Int.ofNat ((i % (2^256 : Int)).toNat % 2^256)
  simp only [Int.ofNat_eq_natCast]
  omega

-- LIBRARY CANDIDATE: zero tests agree on signed values and their word encodings.
theorem wordOfInt_eq_zero_iff {i : Int} (hi : int256Fits i) :
    EVM.wordOfInt i = (⟨0⟩ : UInt256) ↔ i = 0 := by
  constructor
  · intro hz
    have he := congrArg EVM.signed hz
    rw [signed_wordOfInt hi] at he
    exact he
  · rintro rfl
    rfl

theorem signed_eq_zero_iff (w : UInt256) : EVM.signed w = 0 ↔ w = (⟨0⟩ : UInt256) := by
  constructor
  · intro hz
    have he := congrArg EVM.wordOfInt hz
    rw [wordOfInt_signed] at he
    exact he
  · rintro rfl
    rfl

end Benchmarks.UniswapV4PoolManager
