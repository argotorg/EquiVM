import Benchmarks.Midnight.PackedUint128

/-! Word arithmetic and source evaluation for the position's uint128 fields. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def low128 (w : UInt256) : UInt256 := UInt256.land w uint128Mask

theorem low128_toNat (w : UInt256) : (low128 w).toNat = w.toNat % 2 ^ 128 := by
  rw [low128, uland_toNat]
  exact nat_land_mask_eq_mod _ 128

theorem low128_lt (w : UInt256) : (low128 w).toNat < 2 ^ 128 :=
  u256LandMaskToNatLtOfToNat _ _ (by decide)

theorem uint128_product_bound {a b : UInt256}
    (ha : a.toNat < 2 ^ 128) (hb : b.toNat < 2 ^ 128) :
    a.toNat * b.toNat < UInt256.size := by
  calc a.toNat * b.toNat ≤ (2 ^ 128 - 1) * (2 ^ 128 - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    _ < UInt256.size := by decide

def complement128 (w : UInt256) : UInt256 := UInt256.sub uint128Mask w

theorem complement128_toNat {w : UInt256} (hw : w.toNat < 2 ^ 128) :
    (complement128 w).toNat = 2 ^ 128 - 1 - w.toNat := by
  apply usub_toNat
  change w.toNat ≤ 340282366920938463463374607431768211455
  omega

theorem complement128_lt {w : UInt256} (hw : w.toNat < 2 ^ 128) :
    (complement128 w).toNat < 2 ^ 128 := by
  rw [complement128_toNat hw]
  omega

theorem complement128_pos {w : UInt256} (hw : w.toNat < 2 ^ 128 - 1) :
    0 < (complement128 w).toNat := by
  rw [complement128_toNat (by omega)]
  omega

theorem complement128_guard {w : UInt256} (hw : w.toNat < 2 ^ 128) :
    UInt256.gt (complement128 w) uint128Mask = ⟨0⟩ := by
  apply ugt_zero
  have h := complement128_lt hw
  change _ ≤ 340282366920938463463374607431768211455
  omega

theorem evalCast128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {w : UInt256}
    (he : evalExpr? cfg frame evm expr = .ok (.int w.toNat)) :
    evalExpr? cfg frame evm (.cast expr (.elem (.int packedUInt128Int))) =
      .ok (.int (low128 w).toNat) := by
  rw [evalExpr_cast_int he, low128_toNat]
  simp only [normalizeInt, packedUInt128Int, EVM.twoPow, Int.natCast_emod, Int.ofNat_eq_natCast]

theorem evalInRange128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {w : UInt256}
    (he : evalExpr? cfg frame evm expr = .ok (.int w.toNat))
    (hw : w.toNat < 2 ^ 128) :
    evalExpr? cfg frame evm (.inRange packedUInt128Int expr) = .ok (.int w.toNat) := by
  simp only [evalExpr?, he, packedUInt128Int, EvalResult.bind, bind]
  have hlo : ¬ (w.toNat : Int) < 0 := by omega
  have hhi : ¬ (w.toNat : Int) ≥ 2 ^ 128 := by exact_mod_cast (not_le.mpr hw)
  simp only [hlo, hhi, decide_false, Bool.false_or, Bool.false_eq_true, if_false, pure]

theorem evalCheckedSub128 {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat))
    (hbound : a.toNat < 2 ^ 128) (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg frame evm (.inRange packedUInt128Int (.binary .sub lhs rhs)) =
      .ok (.int (UInt256.sub a b).toNat) := by
  apply evalInRange128
  · rw [evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
    simp only [EvalResult.bind, bind, evalBinaryOp?, usub_toNat hle, Int.ofNat_sub hle]
  · rw [usub_toNat hle]; omega

theorem evalCheckedSubUnderflow {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256} (bits : ABI.BitWidth)
    (ha : evalExpr? cfg frame evm lhs = .ok (.int a.toNat))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int b.toNat))
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg frame evm (.inRange (.uint bits) (.binary .sub lhs rhs)) = .revert := by
  rw [evalExpr?, evalExpr_binary_nonshort (by decide) (by decide), ha, hb]
  simp only [EvalResult.bind, bind, evalBinaryOp?]
  have hneg : (a.toNat : Int) - b.toNat < 0 := by omega
  simp only [hneg, decide_true, Bool.true_or, if_true]

end Benchmarks.Midnight
