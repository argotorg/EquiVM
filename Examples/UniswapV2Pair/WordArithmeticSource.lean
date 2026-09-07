import Reasoning.SolmBody
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
namespace UniswapV2Pair

-- LIBRARY CANDIDATE: range-check a canonical EVM word produced by any source expression.
theorem evalExpr_uint256_inRange {cfg : Config} {caller : Frame} {evm : EVM.State}
    {e : Expr} {word : UInt256} (he : evalExpr? cfg caller evm e = .ok (uint256Value word)) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) e) = .ok (uint256Value word) := by
  simp only [evalExpr?, he, EvalResult.bind, bind, uint256Value]
  have hbound := word.val.isLt
  change word.toNat < 2 ^ 256 at hbound
  have hn : ¬ Int.ofNat word.toNat < 0 := by simp only [Int.ofNat_eq_natCast]; omega
  have hh : ¬ Int.ofNat word.toNat ≥ 2 ^ 256 := by simp only [Int.ofNat_eq_natCast]; omega
  simp only [hn, hh, decide_false, Bool.false_or, Bool.false_eq_true, if_false, pure]

-- LIBRARY CANDIDATE: checked multiplication of arbitrary expressions evaluating to EVM words.
theorem evalExpr_uint256_mul {cfg : Config} {caller : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg caller evm rhs = .ok (uint256Value b))
    (hfit : a.toNat * b.toNat < UInt256.size) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) (.binary .mul lhs rhs)) =
      .ok (uint256Value (UInt256.mul a b)) := by
  apply evalExpr_uint256_inRange
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]
  simp only [Int.ofNat_eq_natCast, Nat.cast_mul]

-- LIBRARY CANDIDATE: checked multiplication overflow for arbitrary word-valued expressions.
theorem evalExpr_uint256_mul_overflow {cfg : Config} {caller : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg caller evm rhs = .ok (uint256Value b))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) (.binary .mul lhs rhs)) = .revert := by
  have hge : Int.ofNat (a.toNat * b.toNat) ≥ (2 : Int) ^ 256 := by
    rw [UInt256.size] at hover
    exact Int.ofNat_le.mpr hover
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [if_pos]
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  exact Or.inr (by simpa [Nat.cast_mul] using hge)

-- LIBRARY CANDIDATE: checked subtraction of arbitrary expressions with ordered word values.
theorem evalExpr_uint256_sub {cfg : Config} {caller : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg caller evm rhs = .ok (uint256Value b))
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) (.binary .sub lhs rhs)) =
      .ok (uint256Value (UInt256.sub a b)) := by
  apply evalExpr_uint256_inRange
  simp only [evalExpr?, ha, hb, EvalResult.bind, bind, uint256Value, evalBinaryOp?]
  rw [usub_toNat hle]
  simp only [Int.ofNat_eq_natCast, Int.ofNat_sub hle]

end UniswapV2Pair
