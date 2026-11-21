import Benchmarks.Midnight.WordBitSource

/-! Source expression rules for the uint128 bitmap operations. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

theorem normalizeUint128Word {w : UInt256} (hw : w.toNat < 2^128) :
    normalizeInt packedUInt128Int (w.toNat : Int) = w.toNat := by
  apply normalizeInt_uint_eq_self
  · positivity
  · change (w.toNat : Int) < ((2^128 : Nat) : Int)
    exact_mod_cast hw

theorem evalWordBitOr {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat)) :
    evalExpr? cfg frame evm (.binary (.bitOr (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (.int (UInt256.lor a b).toNat) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise, IntType.bitWidth,
    normalizeWordInt, Int.toNat_natCast, ← u256_lor_toNat_exact, normalizeWordInt]
  rfl

theorem evalUint128BitAnd {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat))
    (ha128 : a.toNat < 2^128) (hb128 : b.toNat < 2^128) :
    evalExpr? cfg frame evm (.binary (.bitAnd packedUInt128Int) lhs rhs) =
      .ok (.int (UInt256.land a b).toNat) := by
  have hl : (UInt256.land a b).toNat < 2^128 := by
    rw [uland_toNat]; exact Nat.and_le_left.trans_lt ha128
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [bind, EvalResult.bind, evalBinaryOp?, evalIntBitwise,
    show IntType.uint packedUInt128Int.bitWidth = packedUInt128Int from rfl,
    normalizeUint128Word ha128, normalizeUint128Word hb128, Int.toNat_natCast]
  rw [show Nat.land a.toNat b.toNat = (UInt256.land a b).toNat from (uland_toNat a b).symm,
    Int.ofNat_eq_natCast, normalizeUint128Word hl]

theorem evalUint128ShiftRight {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {w shift : UInt256}
    (hw : evalExpr? cfg frame evm lhs = .ok (.int w.toNat))
    (hs : evalExpr? cfg frame evm rhs = .ok (.int shift.toNat))
    (hw128 : w.toNat < 2^128) (hshift : shift.toNat < 128) :
    evalExpr? cfg frame evm (.binary (.shr packedUInt128Int) lhs rhs) =
      .ok (.int (UInt256.shiftRight w shift).toNat) := by
  rw [evalExpr_binary_nonshort (by decide) (by decide), hw, hs,
    shiftRight_toNat w shift (by omega)]
  simp only [bind, EvalResult.bind, evalBinaryOp?, Int.toNat_natCast]
  change (if 128 ≤ shift.toNat then _ else _) = _
  rw [if_neg (by omega), normalizeUint128Word hw128]
  simp only [EVM.twoPow, Int.ofNat_eq_natCast, Int.natCast_ediv]

theorem evalWrappingAdd128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat)) :
    evalExpr? cfg frame evm (.cast (.binary .add lhs rhs) (.elem (.int packedUInt128Int))) =
      .ok (.int (low128 (a + b)).toNat) := by
  have he : evalExpr? cfg frame evm (.binary .add lhs rhs) =
      .ok (.int ((a.toNat : Int) + b.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]; rfl
  rw [evalExpr_cast_int he, low128_toNat, uadd_toNat,
    Nat.mod_mod_of_dvd _ (show 2^128 ∣ UInt256.size from by decide)]
  simp only [normalizeInt, packedUInt128Int, EVM.twoPow, Int.natCast_emod, Int.natCast_add]
  rfl

theorem evalWrappingMul128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat)) :
    evalExpr? cfg frame evm (.cast (.binary .mul lhs rhs) (.elem (.int packedUInt128Int))) =
      .ok (.int (low128 (UInt256.mul a b)).toNat) := by
  have he : evalExpr? cfg frame evm (.binary .mul lhs rhs) =
      .ok (.int ((a.toNat : Int) * b.toNat)) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]; rfl
  rw [evalExpr_cast_int he, low128_toNat, u256_mul_toNat,
    Nat.mod_mod_of_dvd _ (show 2^128 ∣ UInt256.size from by decide)]
  simp only [normalizeInt, packedUInt128Int, EVM.twoPow, Int.natCast_emod, Int.natCast_mul]
  rfl

theorem evalCastSub128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat)) (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg frame evm (.cast (.binary .sub lhs rhs) (.elem (.int packedUInt128Int))) =
      .ok (.int (low128 (UInt256.sub a b)).toNat) := by
  apply evalCast128
  rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [EvalResult.bind, bind, evalBinaryOp?, usub_toNat hle, Int.ofNat_sub hle]

end Benchmarks.Midnight
