import Benchmarks.CompoundIII.Comet.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: address equality from the evaluations of arbitrary expressions.
theorem evalExpr_address_eq {cfg : Config} {frame : Frame} {evm : EVM.State}
    {left right : Expr} {a b : AccountAddress}
    (hl : evalExpr? cfg frame evm left = .ok (.address a))
    (hr : evalExpr? cfg frame evm right = .ok (.address b)) :
    evalExpr? cfg frame evm (.binary .eq left right) = .ok (.bool (decide (a = b))) := by
  simp only [evalExpr?, hl, hr, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

-- LIBRARY CANDIDATE: address inequality from the evaluations of arbitrary expressions.
theorem evalExpr_address_ne {cfg : Config} {frame : Frame} {evm : EVM.State}
    {left right : Expr} {a b : AccountAddress}
    (hl : evalExpr? cfg frame evm left = .ok (.address a))
    (hr : evalExpr? cfg frame evm right = .ok (.address b)) :
    evalExpr? cfg frame evm (.binary .ne left right) = .ok (.bool (decide (a ≠ b))) := by
  simp only [evalExpr?, hl, hr, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp

-- LIBRARY CANDIDATE: the maximum uint256 sentinel used by full-balance operations.
theorem evalExpr_uint256_max {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {amount : UInt256}
    (ha : evalExpr? cfg frame evm expr = .ok (.int amount.toNat)) :
    evalExpr? cfg frame evm (.binary .eq expr (.intLit (2^256-1))) =
      .ok (.bool (decide (amount = UInt256.lnot ⟨0⟩))) := by
  simp only [evalExpr?, ha, bind, EvalResult.bind, pure, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  constructor
  · intro he; apply u256_inj; change amount.toNat = 2^256-1; omega
  · intro he; rw [he]; rfl

end Benchmarks.CompoundIII.Comet
