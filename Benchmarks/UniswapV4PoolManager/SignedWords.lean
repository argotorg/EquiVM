import Benchmarks.UniswapV4PoolManager.Values

/-! Signed integer casts and their word representations. -/
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 2000000

-- LIBRARY CANDIDATE: normalization preserves every integer in the signed target range.
theorem normalizeSignedSelf (bits : ABI.BitWidth) (i : Int)
    (hlo : -(Int.ofNat (EVM.twoPow (bits.val - 1))) ≤ i)
    (hhi : i < Int.ofNat (EVM.twoPow (bits.val - 1))) :
    normalizeInt (.sint bits) i = i := by
  have hp : EVM.twoPow bits.val = 2 * EVM.twoPow (bits.val - 1) := by
    simp only [EVM.twoPow]
    conv_lhs => rw [← Nat.sub_add_cancel (by have h := bits.property.1; omega : 1 ≤ bits.val)]
    rw [pow_succ]
    omega
  have hpos : 0 < Int.ofNat (EVM.twoPow (bits.val - 1)) := by
    exact Int.natCast_pos.mpr (Nat.pow_pos (by decide))
  have hpInt : Int.ofNat (EVM.twoPow bits.val) = 2 * Int.ofNat (EVM.twoPow (bits.val - 1)) := by
    rw [hp]; simp only [Int.natCast_mul, Int.ofNat_eq_natCast, Int.cast_ofNat_Int]
  simp only [normalizeInt]
  by_cases hi : 0 ≤ i
  · rw [Int.emod_eq_of_lt hi (by omega), if_pos hhi]
  · rw [Int.emod_eq_add_self_emod, Int.emod_eq_of_lt (by omega) (by omega), if_neg (by omega)]
    omega

-- LIBRARY CANDIDATE: the signed interpretation of a word identifies every nonnegative signed value.
theorem signedWord_eq_nat_iff (w : UInt256) (n : Nat) (hn : n < EVM.twoPow 255) :
    normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat w.toNat) = Int.ofNat n ↔ w.toNat = n := by
  rw [normalizeInt_sint256_word]
  have hw := w.val.isLt
  change w.toNat < EVM.wordModulus at hw
  by_cases hlow : w.toNat < EVM.twoPow 255
  · rw [if_pos hlow]; simp only [Int.ofNat_eq_natCast, Int.natCast_inj]
  · rw [if_neg hlow]
    simp only [Int.ofNat_eq_natCast, EVM.wordModulus, EVM.twoPow] at *
    omega

-- LIBRARY CANDIDATE: wordOfInt is the unsigned residue modulo the EVM word modulus.
theorem wordOfInt_eq_mod (i : Int) :
    EVM.wordOfInt i = UInt256.ofNat (i % Int.ofNat EVM.wordModulus).toNat := by
  apply u256_inj
  cases i with
  | ofNat n =>
    simp only [EVM.wordOfInt, Int.ofNat_eq_natCast,
      Int.not_lt.mpr (Int.natCast_nonneg n), if_false, Int.toNat_natCast,
      Int.natCast_emod]
    change n % UInt256.size = (n % UInt256.size) % UInt256.size
    rw [Nat.mod_mod]
  | negSucc n =>
    simp only [EVM.wordOfInt, Int.negSucc_lt_zero, if_true, Int.natAbs_negSucc]
    split
    · rename_i hz
      change 0 = _
      have hmod : (Int.negSucc n % Int.ofNat EVM.wordModulus) = 0 := by
        change (-(Int.ofNat (n + 1))) % Int.ofNat EVM.wordModulus = 0
        simp only [Int.ofNat_eq_natCast, EVM.wordModulus, EVM.twoPow] at *
        omega
      rw [hmod]; rfl
    · rename_i hz
      change (EVM.wordModulus - (n + 1) % EVM.wordModulus) % EVM.wordModulus = _
      have hmod : (Int.negSucc n % Int.ofNat EVM.wordModulus).toNat =
          EVM.wordModulus - (n + 1) % EVM.wordModulus := by
        change ((-(Int.ofNat (n + 1))) % Int.ofNat EVM.wordModulus).toNat = _
        simp only [Int.ofNat_eq_natCast, EVM.wordModulus, EVM.twoPow] at *
        omega
      rw [hmod]
      rfl

-- LIBRARY CANDIDATE: unsigned-256 casts preserve the encoded EVM word.
theorem wordOfInt_normalizeUint256 (i : Int) :
    EVM.wordOfInt (normalizeInt (.uint ⟨256, by decide⟩) i) = EVM.wordOfInt i := by
  rw [wordOfInt_eq_mod, wordOfInt_eq_mod]
  change UInt256.ofNat ((i % Int.ofNat EVM.wordModulus) % Int.ofNat EVM.wordModulus).toNat = _
  rw [Int.emod_emod]

-- LIBRARY CANDIDATE: sign extension preserves a nonnegative int128 word.
theorem signextend128_of_lt (w : UInt256) (hw : w.toNat < 2^127) :
    UInt256.signextend ⟨15⟩ w = w := by
  change (if UInt256.land w ⟨2^127⟩ ≠ ⟨0⟩ then UInt256.lor w ⟨2^256 - 2^127⟩
    else UInt256.land w ⟨2^127 - 1⟩) = w
  have hz : UInt256.land w ⟨2^127⟩ = ⟨0⟩ := by
    apply u256_inj
    rw [uland_toNat]
    change w.toNat &&& 2^127 = 0
    rw [Nat.and_two_pow, Nat.testBit_eq_false_of_lt hw]
    rfl
  rw [if_neg (not_not.mpr hz)]
  exact u256LandMaskCleanOfToNat w ⟨2^127 - 1⟩ (by rfl) hw

-- LIBRARY CANDIDATE: mathematical signed-256 range and its expression check.
def int256Fits (value : Int) : Prop := -(2^255 : Int) ≤ value ∧ value < (2^255 : Int)
instance (value : Int) : Decidable (int256Fits value) := inferInstanceAs (Decidable (_ ∧ _))

theorem evalCheckedInt256Add {cfg : Config} {f : Frame} {evm : EVM.State}
    {e0 e1 : Expr} {a b : Int}
    (h0 : evalExpr? cfg f evm e0 = .ok (.int a))
    (h1 : evalExpr? cfg f evm e1 = .ok (.int b)) :
    evalExpr? cfg f evm (.inRange (.sint ⟨256, by decide⟩) (.binary .add e0 e1)) =
      if int256Fits (a + b) then .ok (.int (a + b)) else .revert := by
  simp only [evalExpr?, h0, h1, bind, EvalResult.bind, evalBinaryOp?]
  by_cases hf : int256Fits (a + b)
  · rw [if_pos hf]
    have hl : ¬a + b < -(2^(256-1) : Int) := by have h := hf.1; norm_num at *; omega
    have hh : ¬a + b ≥ (2^(256-1) : Int) := by have h := hf.2; norm_num at *; omega
    simp only [hl, hh, decide_false, Bool.false_or, Bool.false_eq_true, if_false, pure]
  · rw [if_neg hf]
    have ho : a + b < -(2^(256-1) : Int) ∨ a + b ≥ (2^(256-1) : Int) := by
      dsimp only [int256Fits] at hf; norm_num at *; omega
    rw [if_pos]
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact ho

-- GENERALIZES Reasoning.Theory.evalExpr_eq_int_true/false to arbitrary frames and both outcomes.
theorem evalIntEq {cfg : Config} {f : Frame} {evm : EVM.State} {lhs rhs : Expr} {a b : Int}
    (ha : evalExpr? cfg f evm lhs = .ok (.int a))
    (hb : evalExpr? cfg f evm rhs = .ok (.int b)) :
    evalExpr? cfg f evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, BEq.beq, Value.int.injEq]

-- LIBRARY CANDIDATE: negate a checked uint256 amount and cast it to int128.
theorem evalNegateInt128Word {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {w : UInt256}
    (he : evalExpr? cfg f evm e = .ok (.int (Int.ofNat w.toNat))) (hfit : w.toNat < 2^127) :
    evalExpr? cfg f evm (.cast (.binary .sub (.intLit 0) e) (.elem (.int (.sint ⟨128, by decide⟩)))) =
      .ok (.int (-(Int.ofNat w.toNat))) := by
  have hs : evalExpr? cfg f evm (.binary .sub (.intLit 0) e) = .ok (.int (-(Int.ofNat w.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    simp only [evalExpr?, he, bind, EvalResult.bind, evalBinaryOp?, pure, zero_sub]
  have hh := evalExpr_cast_int (intType := .sint ⟨128, by decide⟩) hs
  rw [normalizeSignedSelf ⟨128, by decide⟩ _
    (by change -(2^127 : Int) ≤ -(Int.ofNat w.toNat); simp only [Int.ofNat_eq_natCast]; omega)
    (by change -(Int.ofNat w.toNat) < (2^127 : Int); simp only [Int.ofNat_eq_natCast]; omega)] at hh
  exact hh

end Benchmarks.UniswapV4PoolManager
