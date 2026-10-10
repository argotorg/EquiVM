import Benchmarks.UniswapV3.Pool.WordShiftBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

-- LIBRARY CANDIDATE: interpret a full EVM word as a signed source integer.
def signedWordInt (word : UInt256) : Int :=
  normalizeInt (.sint ⟨256, by decide⟩) (Int.ofNat word.toNat)

theorem wordOfInt_signedWordInt (word : UInt256) : EVM.wordOfInt (signedWordInt word) = word := by
  apply u256_inj
  rw [signedWordInt, wordOfInt_normalizeSint_toNat]
  have hw : word.toNat < 2 ^ 256 := word.val.isLt
  change (if word.toNat % 2 ^ 256 < 2 ^ 255 then word.toNat % 2 ^ 256
    else 2 ^ 256 - (2 ^ 256 - word.toNat % 2 ^ 256)) = word.toNat
  rw [Nat.mod_eq_of_lt hw]
  split <;> omega

theorem signedWordInt_wordOfInt (i : Int) :
    signedWordInt (EVM.wordOfInt i) = normalizeInt (.sint ⟨256, by decide⟩) i :=
  normalizeInt_wordOfInt _ _

theorem wordOfInt_normalize256 (i : Int) :
    EVM.wordOfInt (normalizeInt (.sint ⟨256, by decide⟩) i) = EVM.wordOfInt i := by
  rw [← signedWordInt_wordOfInt, wordOfInt_signedWordInt]

-- LIBRARY CANDIDATE: a left shift is multiplication by its power of two, including wrapping.
theorem wordShiftLeft_eq_mul (word : UInt256) (bits : Nat) (hbits : bits < 256) :
    UInt256.shiftLeft word (UInt256.ofNat bits) =
      UInt256.mul word (UInt256.ofNat (2 ^ bits)) := by
  have hb : (UInt256.ofNat bits).toNat = bits :=
    UInt256.toNat_ofNat_of_lt (lt_trans hbits (by decide))
  have hp : (UInt256.ofNat (2 ^ bits)).toNat = 2 ^ bits :=
    UInt256.toNat_ofNat_of_lt (Nat.pow_lt_pow_right (by decide) hbits)
  apply u256_inj
  rw [wordShiftLeft_toNat _ _ (by rw [hb]; exact hbits), u256_mul_toNat, hb, hp]

theorem wordShiftLeft_wordOfInt (i : Int) (bits : Nat) (hbits : bits < 256) :
    UInt256.shiftLeft (EVM.wordOfInt i) (UInt256.ofNat bits) =
      EVM.wordOfInt (i * Int.ofNat (2 ^ bits)) := by
  rw [wordShiftLeft_eq_mul _ _ hbits, wordOfInt_mul, wordOfInt_ofNat_eq]

-- GENERALIZES unsigned source shift evaluation to signed full-width values.
theorem evalExpr_sint_shl {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {i : Int} (bits : Nat) (hbits : bits < 256)
    (he : evalExpr? cfg frame evm expr = .ok (.int i)) :
    evalExpr? cfg frame evm
      (.binary (.shl (.sint ⟨256, by decide⟩)) expr (.intLit (Int.ofNat bits))) =
      .ok (.int (signedWordInt (UInt256.shiftLeft (EVM.wordOfInt i) (UInt256.ofNat bits)))) := by
  rw [wordShiftLeft_wordOfInt _ _ hbits, signedWordInt_wordOfInt]
  simp only [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure,
    show ¬ Int.ofNat bits < 0 from Int.not_lt.mpr (Int.natCast_nonneg _), ↓reduceIte]
  change (if 256 ≤ bits then EvalResult.ok (Value.int 0) else _) = _
  rw [if_neg (Nat.not_le.mpr hbits)]
  rfl

-- LIBRARY CANDIDATE: signed OR operates on the same full word patterns as EVM OR.
theorem evalExpr_sint_lor {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {i j : Int}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int i))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int j)) :
    evalExpr? cfg frame evm (.binary (.bitOr (.sint ⟨256, by decide⟩)) lhs rhs) =
      .ok (.int (signedWordInt (UInt256.lor (EVM.wordOfInt i) (EVM.wordOfInt j)))) := by
  simp only [evalExpr?, ha, hb, evalBinaryOp?, evalIntBitwise, bind, EvalResult.bind,
    IntType.bitWidth, normalizeUInt256_int]
  rw [signedWordInt, u256_lor_toNat_exact]
  rfl

theorem evalExpr_sint_mul {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {i j : Int}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int i))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int j)) :
    evalExpr? cfg frame evm (.cast (.binary .mul lhs rhs)
      (.elem (.int (.sint ⟨256, by decide⟩)))) =
      .ok (.int (signedWordInt (UInt256.mul (EVM.wordOfInt i) (EVM.wordOfInt j)))) := by
  rw [← wordOfInt_mul, signedWordInt_wordOfInt]
  simp only [evalExpr?, ha, hb, castValue?, evalBinaryOp?, bind, EvalResult.bind, EvalResult.ofOption]

end Benchmarks.UniswapV3.Pool
