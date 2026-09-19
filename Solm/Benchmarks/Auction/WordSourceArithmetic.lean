import Solm.Benchmarks.Auction.RangeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Auction

-- LIBRARY CANDIDATE: source arithmetic on nonnegative uint256 values.
theorem checkedMulSourceOk {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hno : a.toNat * b.toNat < UInt256.size) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .mul lhs rhs)) =
      .ok (.int (Int.ofNat (UInt256.mul a b).toNat)) := by
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hno]
  apply uint256RangeSourceOk ?_ hno
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem checkedMulSourceOverflow {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .mul lhs rhs)) =
      .revert := by
  apply uint256RangeSourceOverflow ?_ hover
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  rfl

theorem divSourceOk {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hn : b ≠ ⟨0⟩) :
    evalExpr? cfg solm evm (.binary .div lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.div a b).toNat)) := by
  have hz : (b.toNat : Int) ≠ 0 := by
    intro he
    exact hn (uint256_toNat_eq_zero (by omega))
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?,
    udiv_toNat, Int.ofNat_eq_natCast, hz, if_false, Int.natCast_ediv]

theorem subSourceOk {cfg solm evm lhs rhs a b}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat (UInt256.toNat a))))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat (UInt256.toNat b))))
    (hn : b.toNat ≤ a.toNat) :
    evalExpr? cfg solm evm (.binary .sub lhs rhs) =
      .ok (.int (Int.ofNat (UInt256.sub a b).toNat)) := by
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?,
    usub_toNat hn, Int.ofNat_eq_natCast, Int.natCast_sub hn]

end Auction
