import Benchmarks.Safe.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- GENERALIZES Reasoning.Theory.evalExpr_checkedSub256_revert to arbitrary caller frames.
theorem checkedSubSourceUnderflow {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b))
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg frame evm (.inRange (.uint ⟨256, by decide⟩) (.binary .sub lhs rhs)) =
      .revert := by
  simp [evalExpr?, ha, hb, uint256Value, evalBinaryOp?, bind, EvalResult.bind]
  omega

-- LIBRARY CANDIDATE: unsigned word shifts use modular Solidity integer semantics.
theorem shiftLeftSourceOk {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a n : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hn : evalExpr? cfg frame evm rhs = .ok (uint256Value n)) (hb : n.toNat < 256) :
    evalExpr? cfg frame evm (.binary (.shl (.uint ⟨256, by decide⟩)) lhs rhs) =
      .ok (uint256Value (UInt256.shiftLeft a n)) := by
  have hs : (UInt256.shiftLeft a n).toNat = (a.toNat * 2 ^ n.toNat) % UInt256.size := by
    unfold UInt256.shiftLeft
    rw [if_neg (show ¬ n.val ≥ 256 from by change ¬ n.toNat ≥ 256; omega)]
    unfold UInt256.toNat
    rw [Fin.shiftLeft_val, Nat.shiftLeft_eq]
  simp only [evalExpr?, ha, hn, uint256Value, bind, EvalResult.bind, evalBinaryOp?,
    Int.ofNat_eq_natCast, Int.natCast_nonneg, not_lt.mpr (Int.natCast_nonneg _),
    if_false, IntType.bitWidth, Int.toNat_natCast, Nat.not_le.mpr hb,
    normalizeInt, EVM.twoPow, hs, ← Int.natCast_mul, ← Int.natCast_emod]
  rfl

-- LIBRARY CANDIDATE: the maximum of two bounded words is itself a bounded word.
def maximumWord (a b : UInt256) : UInt256 := UInt256.ofNat (max a.toNat b.toNat)

theorem maximumWord_toNat (a b : UInt256) :
    (maximumWord a b).toNat = max a.toNat b.toNat :=
  ulit_toNat' _ (max_lt a.val.isLt b.val.isLt)

theorem maximumSourceOk {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg frame evm rhs = .ok (uint256Value b)) :
    evalExpr? cfg frame evm (.ite (.binary .gt lhs rhs) lhs rhs) =
      .ok (uint256Value (maximumWord a b)) := by
  simp only [evalExpr?, ha, hb, uint256Value, maximumWord_toNat, bind, EvalResult.bind,
    evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_lt]
  by_cases h : b.toNat < a.toNat
  · simp [h, max_eq_left (le_of_lt h)]
  · simp [h, max_eq_right (by omega : a.toNat ≤ b.toNat)]

end Benchmarks.Safe
