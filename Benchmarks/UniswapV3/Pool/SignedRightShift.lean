import Benchmarks.UniswapV3.Pool.WordComplements

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem wordSar_eq (word count : UInt256) :
    UInt256.sar count word = if 2 ^ 255 ≤ word.toNat then
      UInt256.lnot (UInt256.shiftRight (UInt256.lnot word) count)
    else UInt256.shiftRight word count := by
  have hzero : ¬ (⟨0⟩ : UInt256).toNat ≥ 2 ^ 255 := by decide
  have hlt : ¬ word < (⟨0⟩ : UInt256) := by change ¬ word.toNat < 0; omega
  by_cases h : 2 ^ 255 ≤ word.toNat
  · simp only [UInt256.sar, UInt256.sltBool, if_pos h, if_neg hzero, ↓reduceIte,
      wordComplement_eq_lnot]
    rfl
  · simp only [UInt256.sar, UInt256.sltBool, if_neg h, if_neg hzero, hlt, decide_false,
      Bool.false_eq_true, ↓reduceIte]
    rfl

-- LIBRARY CANDIDATE: floor division of a negative successor by a positive natural.
theorem negOne_sub_nat_ediv (n d : Nat) (hd : 0 < d) :
    (-1 - Int.ofNat n) / Int.ofNat d = -1 - Int.ofNat (n / d) := by
  cases d with
  | zero => omega
  | succ d =>
    have hn : -1 - Int.ofNat n = Int.negSucc n := by
      simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
      omega
    rw [hn]
    change Int.negSucc (n / (d + 1)) = -1 - Int.ofNat (n / (d + 1))
    simp only [Int.ofNat_eq_natCast, Int.negSucc_eq]
    omega

-- LIBRARY CANDIDATE: signed EVM right shift is floor division of the signed integer.
theorem signedWordInt_sar (word : UInt256) (bits : Nat) (hbits : bits < 256) :
    signedWordInt (UInt256.sar (UInt256.ofNat bits) word) =
      signedWordInt word / Int.ofNat (2 ^ bits) := by
  have hb : (UInt256.ofNat bits).toNat = bits :=
    UInt256.toNat_ofNat_of_lt (lt_trans hbits (by decide))
  have hw : word.toNat < 2 ^ 256 := word.val.isLt
  have hshr (w : UInt256) : (UInt256.shiftRight w (UInt256.ofNat bits)).toNat = w.toNat / 2 ^ bits := by
    rw [wordShiftRight_toNat _ _ (by rw [hb]; exact hbits), hb]
  rw [wordSar_eq]
  by_cases hsign : 2 ^ 255 ≤ word.toNat
  · have hc : (UInt256.lnot word).toNat < 2 ^ 255 := by rw [lnot_toNat_gen]; omega
    have hq : (UInt256.shiftRight (UInt256.lnot word) (UInt256.ofNat bits)).toNat < 2 ^ 255 := by
      rw [hshr]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hc
    have hi : signedWordInt word = -1 - Int.ofNat (UInt256.lnot word).toNat := by
      have hn := signedWordInt_lnot word
      rw [signedWordInt_of_lt _ hc] at hn
      omega
    rw [if_pos hsign, signedWordInt_lnot, signedWordInt_of_lt _ hq, hshr, hi]
    exact (negOne_sub_nat_ediv _ _ (Nat.two_pow_pos bits)).symm
  · have hc : word.toNat < 2 ^ 255 := Nat.lt_of_not_ge hsign
    have hq : (UInt256.shiftRight word (UInt256.ofNat bits)).toNat < 2 ^ 255 := by
      rw [hshr]
      exact lt_of_le_of_lt (Nat.div_le_self _ _) hc
    rw [if_neg hsign, signedWordInt_of_lt _ hq, signedWordInt_of_lt _ hc, hshr]
    exact Int.natCast_ediv _ _

theorem evalExpr_sint_sar {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {i : Int} (bits : Nat) (hbits : bits < 256)
    (he : evalExpr? cfg frame evm expr = .ok (.int i)) :
    evalExpr? cfg frame evm
      (.binary (.shr (.sint ⟨256, by decide⟩)) expr (.intLit (Int.ofNat bits))) =
      .ok (.int (signedWordInt (UInt256.sar (UInt256.ofNat bits) (EVM.wordOfInt i)))) := by
  rw [signedWordInt_sar _ _ hbits, signedWordInt_wordOfInt]
  simp only [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure,
    show ¬ Int.ofNat bits < 0 from Int.not_lt.mpr (Int.natCast_nonneg _), ↓reduceIte]
  change (if 256 ≤ bits then _ else _) = _
  rw [if_neg (Nat.not_le.mpr hbits)]
  rfl

theorem normalizeInt_signedWordInt (ty : ABI.IntType) (word : UInt256) :
    normalizeInt ty (signedWordInt word) = normalizeInt ty (Int.ofNat word.toNat) := by
  rw [← normalizeInt_wordOfInt ty (signedWordInt word), wordOfInt_signedWordInt]

theorem evalExpr_sint_sar_narrow {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {i : Int} (width : ABI.BitWidth) (bits : Nat) (hbits : bits < 256)
    (he : evalExpr? cfg frame evm expr = .ok (.int i)) :
    evalExpr? cfg frame evm
      (.cast (.binary (.shr (.sint ⟨256, by decide⟩)) expr (.intLit (Int.ofNat bits)))
        (.elem (.int (.sint width)))) =
      .ok (.int (normalizeInt (.sint width)
        (Int.ofNat (UInt256.sar (UInt256.ofNat bits) (EVM.wordOfInt i)).toNat))) := by
  have hs := evalExpr_sint_sar bits hbits he
  simp only [evalExpr?, hs, castValue?, EvalResult.ofOption, bind, EvalResult.bind,
    normalizeInt_signedWordInt]

end Benchmarks.UniswapV3.Pool
