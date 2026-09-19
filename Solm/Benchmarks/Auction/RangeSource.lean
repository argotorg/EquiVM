import Solm.Benchmarks.Auction.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: the uint256 range check for any natural-valued expression.
theorem uint256RangeSourceOk {cfg solm evm expr} {n : Nat}
    (he : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat n)))
    (hn : n < UInt256.size) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) expr) =
      .ok (.int (Int.ofNat n)) := by
  have hi0 : ¬ Int.ofNat n < 0 := by simp only [Int.ofNat_eq_natCast]; omega
  have hi : ¬ Int.ofNat n ≥ 2 ^ 256 := by
    change n < 2 ^ 256 at hn
    simp only [Int.ofNat_eq_natCast]
    omega
  simp only [evalExpr?, he, bind, EvalResult.bind, hi0, hi, decide_false, Bool.or_self,
    Bool.false_eq_true, if_false, pure]

theorem uint256RangeSourceOverflow {cfg solm evm expr} {n : Nat}
    (he : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat n)))
    (hn : UInt256.size ≤ n) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) expr) = .revert := by
  have hi : Int.ofNat n ≥ 2 ^ 256 := by
    change 2 ^ 256 ≤ n at hn
    simp only [Int.ofNat_eq_natCast]
    omega
  simp only [evalExpr?, he, bind, EvalResult.bind, hi, decide_true, Bool.or_true, if_true]

-- LIBRARY CANDIDATE: evaluate a checked uint256 sum from its two word-valued operands.
theorem checkedAddSourceOk {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hno : a.toNat + b.toNat < UInt256.size) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .add lhs rhs)) =
      .ok (.int (Int.ofNat (a + b).toNat)) := by
  have hw : (a + b).toNat = a.toNat + b.toNat := addWord_toNat a b hno
  rw [hw]
  apply uint256RangeSourceOk ?_ hno
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem checkedAddSourceOverflow {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hover : UInt256.size ≤ a.toNat + b.toNat) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .add lhs rhs)) =
      .revert := by
  apply uint256RangeSourceOverflow ?_ hover
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

end Auction
