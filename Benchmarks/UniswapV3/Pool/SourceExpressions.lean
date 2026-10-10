import Benchmarks.UniswapV3.Pool.Common

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: evaluate a local binding in an arbitrary frame, including immutables.
theorem evalExpr_var_get {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {value : Value} (h : frame.locals.get? name = some value) :
    evalExpr? cfg frame evm (.var name) = .ok value := by
  simp only [evalExpr?, h, EvalResult.ofOption]

-- LIBRARY CANDIDATE: compositional Boolean conjunction for arbitrary source frames.
theorem evalExpr_bool_and {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Bool}
    (ha : evalExpr? cfg frame evm lhs = .ok (.bool a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.bool b)) :
    evalExpr? cfg frame evm (.binary .and lhs rhs) = .ok (.bool (a && b)) := by
  cases a <;> simp only [evalExpr?, ha, hb, bind, EvalResult.bind, pure,
    Bool.false_and, Bool.true_and]

-- GENERALIZES Reasoning.SolmArithmetic.evalExpr_or_false_right and evalExpr_or_true_left.
theorem evalExpr_bool_or {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Bool}
    (ha : evalExpr? cfg frame evm lhs = .ok (.bool a))
    (hb : evalExpr? cfg frame evm rhs = .ok (.bool b)) :
    evalExpr? cfg frame evm (.binary .or lhs rhs) = .ok (.bool (a || b)) := by
  cases a <;> simp only [evalExpr?, ha, hb, bind, EvalResult.bind, pure,
    Bool.false_or, Bool.true_or]

-- LIBRARY CANDIDATE: unsigned shifts on natural source values without overflow.
theorem evalExpr_uintShiftLeft {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} (width : ABI.BitWidth) (value bits : Nat)
    (heval : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat value)))
    (hbits : bits < width.val) (hfit : value * 2 ^ bits < 2 ^ width.val) :
    evalExpr? cfg frame evm (.binary (.shl (.uint width)) expr (.intLit (Int.ofNat bits))) =
      .ok (.int (Int.ofNat (value * 2 ^ bits))) := by
  simp only [evalExpr?, heval, bind, EvalResult.bind, pure, evalBinaryOp?]
  simp only [Int.ofNat_eq_natCast, if_neg (Int.not_lt.mpr (Int.natCast_nonneg bits)), ↓reduceIte,
    IntType.bitWidth, Int.toNat_natCast, Nat.not_le.mpr hbits]
  rw [normalizeInt_uint_eq_self _ _ (by positivity) (by
    simp only [EVM.twoPow, Int.ofNat_eq_natCast, Nat.cast_pow, Nat.cast_ofNat]
    exact_mod_cast hfit)]
  simp [EVM.twoPow]

-- LIBRARY CANDIDATE: unsigned right shift evaluates at any natural source value.
theorem evalExpr_uintShiftRight {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} (width : ABI.BitWidth) (value bits : Nat)
    (heval : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat value)))
    (hbits : bits < width.val) :
    evalExpr? cfg frame evm (.binary (.shr (.uint width)) expr (.intLit (Int.ofNat bits))) =
      .ok (.int (normalizeInt (.uint width) (Int.ofNat value) / Int.ofNat (2 ^ bits))) := by
  simp only [evalExpr?, heval, bind, EvalResult.bind, pure, evalBinaryOp?]
  simp only [Int.ofNat_eq_natCast, if_neg (Int.not_lt.mpr (Int.natCast_nonneg bits)), ↓reduceIte,
    IntType.bitWidth, Int.toNat_natCast, Nat.not_le.mpr hbits, EVM.twoPow]

-- GENERALIZES Reasoning.SolmArithmetic integer equality to arbitrary frames and expressions.
theorem evalExpr_nat_eq_zero {cfg : Config} {frame : Frame} {evm : EVM.State}
    {expr : Expr} {n : Nat} (he : evalExpr? cfg frame evm expr = .ok (.int (Int.ofNat n))) :
    evalExpr? cfg frame evm (.binary .eq expr (.intLit 0)) = .ok (.bool (decide (n = 0))) := by
  simp [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure]
  apply Bool.eq_iff_iff.mpr
  simp

-- LIBRARY CANDIDATE: the length of a local byte array in an arbitrary frame.
theorem evalExpr_localBytesLength {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {out : ByteArray} (hget : frame.locals.get? name = some (.bytes out)) :
    evalExpr? cfg frame evm (.arrayLength .localVar ⟨name, []⟩) = .ok (.int (Int.ofNat out.size)) := by
  simp only [evalExpr?, hget, readLocalPath?, bind, EvalResult.bind, pure]

-- GENERALIZES Reasoning.SolmArithmetic.assignLocalVarBase_ok to arbitrary frames.
theorem assignLocalVarBase_frame {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value} (hget : frame.locals.get? name = some old) :
    assignStorageRef? cfg frame evm .localVar ⟨name, []⟩ value =
      .ok ({ frame with locals := frame.locals.insert name value }, evm) := by
  simp only [assignStorageRef?, hget, updateLocalPath?, bind, EvalResult.bind, pure]

-- LIBRARY CANDIDATE: unsigned word comparisons in arbitrary source frames.
theorem evalExpr_word_gt {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm (.binary .gt lhs rhs) =
      .ok (.bool (decide (b.toNat < a.toNat))) := by
  simp [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]

theorem evalExpr_word_eq {cfg : Config} {frame : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg frame evm lhs = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? cfg frame evm rhs = .ok (.int (Int.ofNat b.toNat))) :
    evalExpr? cfg frame evm (.binary .eq lhs rhs) = .ok (.bool (decide (a = b))) := by
  simp [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, decide_eq_true_eq, Value.int.injEq, Int.natCast_inj]
  exact ⟨u256_inj, fun h => congrArg UInt256.toNat h⟩

end Benchmarks.UniswapV3.Pool
