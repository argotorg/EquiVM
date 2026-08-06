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
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) (.binary (.mul (.uint ⟨256, by decide⟩) .checked) lhs rhs)) =
      .ok (uint256Value (UInt256.mul a b)) := by
  exact evalExpr_checked_mul_uint256_word_ok ha hb
    (by rw [u256_mul_toNat, Nat.mod_eq_of_lt hfit]) hfit

-- LIBRARY CANDIDATE: checked multiplication overflow for arbitrary word-valued expressions.
theorem evalExpr_uint256_mul_overflow {cfg : Config} {caller : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg caller evm rhs = .ok (uint256Value b))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) (.binary (.mul (.uint ⟨256, by decide⟩) .checked) lhs rhs)) = .revert := by
  exact evalExpr_checked_mul_uint256_word_revert_of_overflow ha hb hover

-- LIBRARY CANDIDATE: checked subtraction of arbitrary expressions with ordered word values.
theorem evalExpr_uint256_sub {cfg : Config} {caller : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg caller evm rhs = .ok (uint256Value b))
    (hle : b.toNat ≤ a.toNat) :
    evalExpr? cfg caller evm (.inRange (.uint ⟨256, by decide⟩) (.binary (.sub (.uint ⟨256, by decide⟩) .checked) lhs rhs)) =
      .ok (uint256Value (UInt256.sub a b)) := by
  exact evalExpr_checked_sub_uint256_word_ok ha hb (usub_toNat hle) hle

end UniswapV2Pair
