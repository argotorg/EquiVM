import Benchmarks.Midnight.InternalCall
import Benchmarks.Midnight.SourceControl
import Benchmarks.Midnight.PositionViewSourceBase

/-! Saturating word subtraction and the source helper implementing it. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def zeroFloorSubWord (x y : UInt256) : UInt256 := UInt256.ofNat (x.toNat - y.toNat)

-- LIBRARY CANDIDATE: natural subtraction is already within the unsigned word range.
theorem zeroFloorSubWord_toNat (x y : UInt256) :
    (zeroFloorSubWord x y).toNat = x.toNat - y.toNat :=
  UInt256.toNat_ofNat_of_lt ((Nat.sub_le _ _).trans_lt x.val.isLt)

-- LIBRARY CANDIDATE: Solidity's branchless saturating-subtraction idiom.
theorem zeroFloorSubWord_eq (x y : UInt256) :
    UInt256.mul (UInt256.gt x y) (UInt256.sub x y) = zeroFloorSubWord x y := by
  apply u256_inj
  rw [zeroFloorSubWord_toNat]
  by_cases h : y.toNat < x.toNat
  · rw [ugt_one h, u256_mul_toNat, usub_toNat (by omega)]
    change (1 * (x.toNat - y.toNat)) % UInt256.size = _
    rw [Nat.one_mul]
    exact Nat.mod_eq_of_lt ((Nat.sub_le x.toNat y.toNat).trans_lt x.val.isLt)
  · rw [ugt_zero (by omega), u256_mul_zero_left]
    change 0 = x.toNat - y.toNat
    omega

abbrev zeroFloorSubFunction : FunctionDecl := contract.functions[5]!

theorem zeroFloorSubSource {cfg : Config} {frame : Frame} {evm : State} {x y : UInt256}
    (hx : frame.locals.get? "x" = some (.int x.toNat))
    (hy : frame.locals.get? "y" = some (.int y.toNat)) :
    ExecFuncBody cfg frame evm zeroFloorSubFunction.body
      (.returned frame evm (some [.int (zeroFloorSubWord x y).toNat])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have he : evalExpr? cfg frame evm
      (.ite (.binary .gt (.var "x") (.var "y"))
        (.binary .sub (.var "x") (.var "y")) (.intLit 0)) =
      .ok (.int (zeroFloorSubWord x y).toNat) := by
    by_cases h : y.toNat < x.toNat
    · simp only [evalExpr?, hx, hy, EvalResult.ofOption, bind, pure, EvalResult.bind,
        evalBinaryOp?, Int.ofNat_lt, h, decide_true, zeroFloorSubWord_toNat]
      congr 2
      exact (Int.natCast_sub (by omega)).symm
    · simp only [evalExpr?, hx, hy, EvalResult.ofOption, bind, pure, EvalResult.bind,
        evalBinaryOp?, Int.ofNat_lt, h, decide_false, zeroFloorSubWord_toNat,
        Nat.sub_eq_zero_of_le (by omega : x.toNat ≤ y.toNat)]
      rfl
  simp only [evalExprs?, he, bind, pure, EvalResult.bind]

theorem callZeroFloorSub {cfg : Config} {frame : Frame} {evm : State}
    {x y : UInt256} {args : List Expr} {name : Ident}
    (hc : frame.contract = contract)
    (ha : evalExprs? cfg frame evm args = .ok [.int x.toNat, .int y.toNat]) :
    ExecStmt cfg frame evm (.internalCall "UtilsLib_zeroFloorSub" args name)
      (.ok (wordLocal frame name (zeroFloorSubWord x y)) evm) := by
  let locals := ((∅ : Store).insert "y" (.int y.toNat)).insert "x" (.int x.toNat)
  apply internalCallFunctionReturn (callee := zeroFloorSubFunction) (locals := locals)
    (value := some [.int (zeroFloorSubWord x y).toNat]) ha
  · rw [hc]; rfl
  · rfl
  · apply zeroFloorSubSource
    · exact store_get_self _ _ _
    · simp only [locals, store_get_ne _ _ (show ("x" == "y") = false from rfl), store_get_self]

end Benchmarks.Midnight
