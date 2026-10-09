import Benchmarks.Morpho.MetaMorphoV1_1.BodyCommon

/-! Shared arithmetic evaluation facts, including checked unsigned results. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: evaluate addition of two nonnegative source integers in any frame.
theorem evalExpr_natAdd {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Nat}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg solm evm (.binary .add lhs rhs) = .ok (.int (Int.ofNat (a + b))) := by
  exact naturalAddSource ha hb

-- LIBRARY CANDIDATE: evaluate an unsigned subtraction clamped at zero.
theorem evalExpr_zeroFloorSub {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : Nat}
    (ha : evalExpr? cfg solm evm lhs = .ok (.int (Int.ofNat a)))
    (hb : evalExpr? cfg solm evm rhs = .ok (.int (Int.ofNat b))) :
    evalExpr? cfg solm evm (.ite (.binary .gt lhs rhs) (.binary .sub lhs rhs) (.intLit 0)) =
      .ok (.int (Int.ofNat (a - b))) := by
  have hcmp : evalExpr? cfg solm evm (.binary .gt lhs rhs) =
      .ok (.bool (decide (b < a))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide)]
    simp only [ha, hb, bind, EvalResult.bind, evalBinaryOpGtInt, gt_iff_lt,
      Int.ofNat_eq_natCast, Int.ofNat_lt]
  rw [evalExpr?, hcmp]
  by_cases h : b < a
  · simp only [h, decide_true, EvalResult.bind, bind]
    simp only [evalExpr?, ha, hb, EvalResult.bind, bind, evalBinaryOp?]
    simp only [Int.ofNat_eq_natCast, Int.ofNat_sub (Nat.le_of_lt h)]
  · have hle : a ≤ b := by omega
    simp only [h, decide_false, EvalResult.bind, bind, evalExpr?, pure,
      Nat.sub_eq_zero_of_le hle]
    rfl

-- LIBRARY CANDIDATE: the EVM gt/mul idiom computes natural subtraction without underflow.
theorem wordZeroFloorSub (a b : UInt256) :
    UInt256.mul (UInt256.gt a b) (UInt256.sub a b) = UInt256.ofNat (a.toNat - b.toNat) := by
  by_cases h : b.toNat < a.toNat
  · rw [ugt_one h]
    apply u256_inj
    rw [u256_mul_toNat, usub_toNat (Nat.le_of_lt h)]
    have hfit : a.toNat - b.toNat < UInt256.size :=
      lt_of_le_of_lt (Nat.sub_le _ _) a.val.isLt
    simp only [show (⟨1⟩ : UInt256).toNat = 1 from rfl, Nat.one_mul,
      Nat.mod_eq_of_lt hfit, UInt256.toNat_ofNat_of_lt hfit]
  · rw [ugt_zero (Nat.le_of_not_gt h), u256_mul_zero_left,
      Nat.sub_eq_zero_of_le (Nat.le_of_not_gt h)]
    rfl

-- LIBRARY CANDIDATE: characterize the solc multiplication guard on a fitting product.
theorem checkedMulGuardOk (a b : UInt256) (hfit : a.toNat * b.toNat < UInt256.size) :
    UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul a b) a) b)
      (UInt256.isZero a)) = ⟨0⟩ := by
  apply isZero_eq_zero_of_ne
  by_cases ha : a = ⟨0⟩
  · rw [ha]
    exact u256_lor_one_right_ne_zero _
  · rw [isZero_eq_zero_of_ne ha, u256_lor_zero, u256_mul_comm a b,
      checkedMul_div_eq ha (by simpa [Nat.mul_comm] using hfit), uInt256_eq_self]
    decide

-- LIBRARY CANDIDATE: characterize the same guard when multiplication overflows.
theorem checkedMulGuardOverflow (a b : UInt256) (hover : UInt256.size ≤ a.toNat * b.toNat) :
    UInt256.isZero (UInt256.lor (UInt256.eq (UInt256.div (UInt256.mul a b) a) b)
      (UInt256.isZero a)) ≠ ⟨0⟩ := by
  have ha : a ≠ ⟨0⟩ := by
    intro hz
    simp only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.zero_mul] at hover
    exact (by decide : ¬ UInt256.size ≤ 0) hover
  rw [isZero_eq_zero_of_ne ha, u256_lor_zero, u256_mul_comm a b,
    u256_eq_of_ne (checkedMul_div_ne (by simpa [Nat.mul_comm] using hover))]
  decide

-- LIBRARY CANDIDATE: a scalar return whose expression reverts propagates that revert.
theorem scalarReturnReverts {cfg : Config} {solm : Frame} {evm : EVM.State} {expr : Expr}
    (he : evalExpr? cfg solm evm expr = .revert) :
    ExecFuncBody cfg solm evm [.return [expr]] .reverted := by
  exact ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.returnRevert (by
    simp only [evalExprs?, he, EvalResult.bind, bind])))

-- GENERALIZES Reasoning.SolmArithmetic.evalExpr_checkedSub256_revert to any frame.
theorem checkedSubSourceUnderflow {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a b : UInt256}
    (ha : evalExpr? cfg solm evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg solm evm rhs = .ok (uint256Value b))
    (hlt : a.toNat < b.toNat) :
    evalExpr? cfg solm evm (.inRange (.uint ⟨256, by decide⟩) (.binary .sub lhs rhs)) =
      .revert := by
  have hnegative : Int.ofNat a.toNat - Int.ofNat b.toNat < 0 := by
    simp only [Int.ofNat_eq_natCast]
    omega
  simp only [evalExpr?, ha, hb, uint256Value, EvalResult.bind, bind, evalBinaryOp?,
    hnegative, decide_true, Bool.true_or, if_true]

-- LIBRARY CANDIDATE: division by zero reverts after its numerator evaluates.
theorem divSourceZero {cfg : Config} {solm : Frame} {evm : EVM.State}
    {lhs rhs : Expr} {a : UInt256}
    (ha : evalExpr? cfg solm evm lhs = .ok (uint256Value a))
    (hb : evalExpr? cfg solm evm rhs = .ok (uint256Value ⟨0⟩)) :
    evalExpr? cfg solm evm (.binary .div lhs rhs) = .revert := by
  simp only [evalExpr?, ha, hb, uint256Value, EvalResult.bind, bind, evalBinaryOp?]
  rfl

-- LIBRARY CANDIDATE: a non-short-circuit binary expression propagates a left-hand revert.
theorem binarySourceRevertLeft {cfg : Config} {solm : Frame} {evm : EVM.State}
    {op : BinaryOp} {lhs rhs : Expr} (hand : op ≠ .and) (hor : op ≠ .or)
    (he : evalExpr? cfg solm evm lhs = .revert) :
    evalExpr? cfg solm evm (.binary op lhs rhs) = .revert := by
  rw [evalExpr_binary_nonshort hand hor, he]
  rfl

-- LIBRARY CANDIDATE: a binary expression propagates a right-hand revert after its left value.
theorem binarySourceRevertRight {cfg : Config} {solm : Frame} {evm : EVM.State}
    {op : BinaryOp} {lhs rhs : Expr} {value : Value} (hand : op ≠ .and) (hor : op ≠ .or)
    (ha : evalExpr? cfg solm evm lhs = .ok value)
    (hb : evalExpr? cfg solm evm rhs = .revert) :
    evalExpr? cfg solm evm (.binary op lhs rhs) = .revert := by
  rw [evalExpr_binary_nonshort hand hor, ha, hb]
  rfl

-- LIBRARY CANDIDATE: a checked range expression propagates its operand's revert.
theorem rangeSourceRevert {cfg : Config} {solm : Frame} {evm : EVM.State}
    {expr : Expr} {ty : IntType} (he : evalExpr? cfg solm evm expr = .revert) :
    evalExpr? cfg solm evm (.inRange ty expr) = .revert := by
  rw [evalExpr?, he]
  rfl

-- GENERALIZES Reasoning.SolmBody.evalExpr_uint256_inRange to arbitrary unsigned widths.
theorem evalExpr_uintInRange {cfg : Config} {solm : Frame} {evm : EVM.State}
    {expr : Expr} {value : Nat} (width : ABI.BitWidth)
    (he : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat value)))
    (hfit : value < 2 ^ width.val) :
    evalExpr? cfg solm evm (.inRange (.uint width) expr) = .ok (.int (Int.ofNat value)) := by
  simp only [evalExpr?, he, EvalResult.bind, bind]
  have hnegative : ¬ Int.ofNat value < 0 := by
    simp only [Int.ofNat_eq_natCast]
    omega
  have hlarge : ¬ Int.ofNat value ≥ (2 : Int) ^ width.val := by
    simp only [Int.ofNat_eq_natCast]
    exact_mod_cast Nat.not_le_of_lt hfit
  simp only [hnegative, hlarge, decide_false, Bool.false_or, Bool.false_eq_true, if_false, pure]

-- LIBRARY CANDIDATE: a nonnegative integer beyond an unsigned range reverts.
theorem evalExpr_uintInRange_revert {cfg : Config} {solm : Frame} {evm : EVM.State}
    {expr : Expr} {value : Nat} (width : ABI.BitWidth)
    (he : evalExpr? cfg solm evm expr = .ok (.int (Int.ofNat value)))
    (hover : 2 ^ width.val ≤ value) :
    evalExpr? cfg solm evm (.inRange (.uint width) expr) = .revert := by
  simp only [evalExpr?, he, EvalResult.bind, bind]
  have hlarge : Int.ofNat value ≥ (2 : Int) ^ width.val := by
    simp only [Int.ofNat_eq_natCast]
    exact_mod_cast hover
  simp only [hlarge, decide_true, Bool.or_true, if_true]

-- LIBRARY CANDIDATE: an internal scalar getter propagates a reverting return expression.
theorem internalCallRevertExpr {cfg : Config} {solm : Frame} {evm : EVM.State}
    {name retVar : Ident} {retTy : List ABIType} {expr : Expr}
    (hlookup : lookupCallable? solm.contract name =
      some { params := [], returnType := retTy, body := [.return [expr]] })
    (heval : evalExpr? cfg { solm with locals := ∅ } evm expr = .revert) :
    ExecStmt cfg solm evm (.internalCall name [] retVar) .reverted := by
  exact ExecStmt.internalCallRevert (by rfl) hlookup rfl
    (ExecFuncBody.execBlockRevert (ExecBlock.consRevert (ExecStmt.returnRevert (by
      simp only [evalExprs?, heval, bind, EvalResult.bind]))))

end Benchmarks.Morpho.MetaMorphoV1_1
