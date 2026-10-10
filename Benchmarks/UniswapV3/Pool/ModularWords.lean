import Benchmarks.UniswapV3.Pool.SignedWords
import Benchmarks.UniswapV3.Pool.Routines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

open scoped Fin.IntCast Fin.CommRing


-- LIBRARY CANDIDATE: bridge the EVM integer encoding to the finite ring representation.
theorem wordOfInt_val_intCast (i : Int) :
    (EVM.wordOfInt i).val = (i : Fin UInt256.size) := by
  rw [Fin.intCast_def]
  by_cases h : 0 ≤ i
  · rw [if_pos h, wordOfInt_nonneg i h]
    have hi : i.natAbs = i.toNat := by omega
    rw [hi]
    rfl
  · rw [if_neg h, EVM.wordOfInt, if_pos (by omega)]
    dsimp only
    by_cases hz : i.natAbs % EVM.wordModulus = 0
    · rw [if_pos hz]
      apply Fin.ext
      simp only [Fin.val_neg', Fin.val_ofNat]
      change 0 = (UInt256.size - i.natAbs % UInt256.size) % UInt256.size
      change i.natAbs % UInt256.size = 0 at hz
      rw [hz, Nat.sub_zero, Nat.mod_self]
    · rw [if_neg hz]
      apply Fin.ext
      rfl


theorem wordOfInt_mod (i : Int) :
    (EVM.wordOfInt i).toNat = (i % (2 ^ 256 : Int)).toNat := by
  change (EVM.wordOfInt i).val.val = _
  rw [wordOfInt_val_intCast, Fin.val_intCast]
  rfl

theorem wordOfInt_add (i j : Int) :
    EVM.wordOfInt (i + j) = UInt256.add (EVM.wordOfInt i) (EVM.wordOfInt j) := by
  apply u256_inj
  change (EVM.wordOfInt (i + j)).val.val =
    ((EVM.wordOfInt i).val + (EVM.wordOfInt j).val).val
  simp only [wordOfInt_val_intCast, Int.cast_add]

theorem wordOfInt_mul (i j : Int) :
    EVM.wordOfInt (i * j) = UInt256.mul (EVM.wordOfInt i) (EVM.wordOfInt j) := by
  apply u256_inj
  change (EVM.wordOfInt (i * j)).val.val =
    ((EVM.wordOfInt i).val * (EVM.wordOfInt j).val).val
  simp only [wordOfInt_val_intCast, Int.cast_mul]


theorem wordOfInt_sub (i j : Int) :
    EVM.wordOfInt (i - j) = UInt256.sub (EVM.wordOfInt i) (EVM.wordOfInt j) := by
  apply u256_inj
  change (EVM.wordOfInt (i - j)).val.val =
    ((EVM.wordOfInt i).val - (EVM.wordOfInt j).val).val
  simp only [wordOfInt_val_intCast, Int.cast_sub]

-- LIBRARY CANDIDATE: Solidity normalization commutes with the ambient EVM word modulus.
theorem normalizeInt_wordOfInt (ty : ABI.IntType) (i : Int) :
    normalizeInt ty (Int.ofNat (EVM.wordOfInt i).toNat) = normalizeInt ty i := by
  have hi : Int.ofNat (EVM.wordOfInt i).toNat = i % (2 ^ 256 : Int) := by
    rw [wordOfInt_mod]
    exact Int.toNat_of_nonneg (Int.emod_nonneg i (by positivity))
  have hres (width : ABI.BitWidth) :
      Int.ofNat (EVM.wordOfInt i).toNat % Int.ofNat (EVM.twoPow width.val) =
        i % Int.ofNat (EVM.twoPow width.val) := by
    rw [hi]
    change (i % (2 ^ 256 : Int)) % (2 ^ width.val : Int) = _
    exact Int.emod_emod_of_dvd i (pow_dvd_pow 2 width.property.2.1)
  cases ty with
  | uint width => exact hres width
  | sint width => simp only [normalizeInt, hres]


theorem normalizeUIntInt_mask (width : ABI.BitWidth) (i : Int) (mask : UInt256)
    (hmask : mask.toNat = 2 ^ width.val - 1) :
    normalizeInt (.uint width) i = Int.ofNat (UInt256.land (EVM.wordOfInt i) mask).toNat := by
  rw [← normalizeInt_wordOfInt (.uint width) i]
  exact normalizeUIntWord_mask width _ mask hmask

theorem signextend_wordOfInt (width : ABI.BitWidth) (a : UInt256) (i : Int)
    (ha : a.toNat ≤ 31)
    (hsign : (UInt256.shiftLeft ⟨1⟩ (UInt256.add (UInt256.mul a ⟨8⟩) ⟨7⟩)).toNat =
      2 ^ (width.val - 1)) :
    UInt256.signextend a (EVM.wordOfInt i) = EVM.wordOfInt (normalizeInt (.sint width) i) := by
  rw [signextend_normalizeSint width a _ ha hsign, normalizeInt_wordOfInt]

theorem normalizeInt_residue (ty : ABI.IntType) (i : Int) :
    normalizeInt ty i % Int.ofNat (EVM.twoPow ty.bitWidth.val) = i % Int.ofNat (EVM.twoPow ty.bitWidth.val) := by
  cases ty with
  | uint width => simp only [normalizeInt, IntType.bitWidth, Int.emod_emod]
  | sint width =>
      simp only [normalizeInt, IntType.bitWidth]
      split <;> simp [Int.sub_emod]

theorem normalizeInt_add_right (ty : ABI.IntType) (i j : Int) :
    normalizeInt ty (i + normalizeInt ty j) = normalizeInt ty (i + j) := by
  have hr : (i + normalizeInt ty j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) =
      (i + j) % Int.ofNat (EVM.twoPow ty.bitWidth.val) := by
    rw [Int.add_emod, normalizeInt_residue, ← Int.add_emod]
  cases ty with
  | uint width => exact hr
  | sint width => simp only [normalizeInt, IntType.bitWidth] at hr ⊢; rw [hr]


theorem normalizeSint_eq_self (width : ABI.BitWidth) (i : Int)
    (hlo : -Int.ofNat (EVM.twoPow (width.val - 1)) ≤ i)
    (hhi : i < Int.ofNat (EVM.twoPow (width.val - 1))) :
    normalizeInt (.sint width) i = i := by
  have hm : Int.ofNat (EVM.twoPow width.val) =
      2 * Int.ofNat (EVM.twoPow (width.val - 1)) := by
    have hw : width.val = (width.val - 1) + 1 := by have := width.property; omega
    conv_lhs => rw [hw]
    simp only [EVM.twoPow, pow_succ, Int.ofNat_eq_natCast, Int.natCast_mul]
    omega
  have hp : 0 < Int.ofNat (EVM.twoPow (width.val - 1)) :=
    Int.ofNat_lt.mpr (Nat.two_pow_pos _)
  simp only [normalizeInt]
  by_cases hn : 0 ≤ i
  · rw [Int.emod_eq_of_lt hn (by omega), if_pos hhi]
  · have hr : i % Int.ofNat (EVM.twoPow width.val) = i + Int.ofNat (EVM.twoPow width.val) := by
      rw [Int.emod_eq_add_self_emod]
      exact Int.emod_eq_of_lt (by omega) (by omega)
    rw [hr, if_neg (by omega)]
    omega

end Benchmarks.UniswapV3.Pool
