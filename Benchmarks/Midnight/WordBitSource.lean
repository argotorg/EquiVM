import Benchmarks.Midnight.BitmapArithmetic
import Benchmarks.Midnight.SourceControl

/-! Source expression rules for wrapping words and bitmap operations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem normalizeWordInt (word : UInt256) :
    normalizeInt (.uint ⟨256, by decide⟩) (word.toNat : Int) = word.toNat :=
  normalizeInt_uint256_word word

-- LIBRARY CANDIDATE: full-width wrapping addition on arbitrary source expressions.
theorem evalWrappingAdd256 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat)) :
    evalExpr? cfg frame evm
      (.cast (.binary .add lhs rhs) (.elem (.int (.uint ⟨256, by decide⟩)))) =
      .ok (.int (a + b).toNat) := by
  have he : evalExpr? cfg frame evm (.binary .add lhs rhs) =
      .ok (.int ((a.toNat : Int) + b.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
    rfl
  rw [evalExpr_cast_int he, uadd_toNat]
  simp only [normalizeInt, EVM.twoPow, Int.natCast_emod, Int.natCast_add]
  rfl

-- LIBRARY CANDIDATE: logical right shift below the word width.
theorem evalWordShiftRight {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {word shift : UInt256}
    (hw : evalExpr? cfg frame evm lhs = .ok (.int word.toNat))
    (hs : evalExpr? cfg frame evm rhs = .ok (.int shift.toNat))
    (hshift : shift.toNat < 256) :
    evalExpr? cfg frame evm (.binary (.shr (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (.int (UInt256.shiftRight word shift).toNat) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hw, hs,
    shiftRight_toNat word shift hshift]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.toNat_natCast]
  change (if 256 ≤ shift.toNat then _ else _) = _
  rw [if_neg (by omega)]
  simp only [normalizeWordInt, EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_ediv]

theorem evalWordBitAnd {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat)) :
    evalExpr? cfg frame evm (.binary (.bitAnd (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (.int (UInt256.land a b).toNat) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise, IntType.bitWidth,
    normalizeWordInt, Int.toNat_natCast]
  have he : Nat.land a.toNat b.toNat = (UInt256.land a b).toNat := (uland_toNat a b).symm
  rw [he, normalizeInt_uint256_word]
  rfl

theorem evalWordBitNot {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {word : UInt256}
    (hw : evalExpr? cfg frame evm expr = .ok (.int word.toNat)) :
    evalExpr? cfg frame evm (.unary (.bitNot (.uint ⟨256, by decide⟩)) expr) =
      .ok (.int (UInt256.lnot word).toNat) := by
  simp only [evalExpr?, hw, bind, EvalResult.bind, evalUnaryOp?, IntType.bitWidth,
    normalizeWordInt, Int.toNat_natCast]
  rw [show EVM.twoPow 256 - 1 - word.toNat = (UInt256.lnot word).toNat from
    (lnot_toNat_gen word).symm, normalizeInt_uint256_word]
  rfl

theorem evalOneShiftLeft {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {bit : UInt256}
    (hb : evalExpr? cfg frame evm expr = .ok (.int bit.toNat)) (hbit : bit.toNat < 256) :
    evalExpr? cfg frame evm
      (.binary (.shl (.uint ⟨256, by decide⟩)) (.intLit 1) expr) =
      .ok (.int (UInt256.shiftLeft (UInt256.ofNat 1) bit).toNat) := by
  have hp : 2^bit.toNat < UInt256.size := Nat.pow_lt_pow_right (by decide) hbit
  rw [evalExpr_binary_nonshort (by decide) (by decide), hb]
  simp only [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?, Int.toNat_natCast]
  change (if 256 ≤ bit.toNat then _ else _) = _
  rw [if_neg (by omega), shiftLeft_toNat_of_noOverflow _ _ hbit
    (by simpa only [show (UInt256.ofNat 1).toNat = 1 from rfl, Nat.one_mul] using hp)]
  simp only [show (UInt256.ofNat 1).toNat = 1 from rfl, Nat.one_mul, Int.one_mul,
    normalizeInt, EVM.twoPow, Int.ofNat_eq_natCast]
  rw [Int.emod_eq_of_lt (by positivity) (by exact_mod_cast hp)]

end Benchmarks.Midnight
