import Benchmarks.Morpho.MorphoBlue.ExactlyOneZero

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev zeroFloorSubFunction : FunctionDecl := contract.functions[17]!

def zeroFloorSubWord (x y : UInt256) : UInt256 :=
  if y.toNat < x.toNat then UInt256.sub x y else UInt256.ofNat 0

-- LIBRARY CANDIDATE: branchless saturating subtraction of unsigned words.
theorem zeroFloorSubWord_evm (x y : UInt256) :
    UInt256.mul (UInt256.gt x y) (UInt256.sub x y) = zeroFloorSubWord x y := by
  by_cases h : y.toNat < x.toNat
  · rw [zeroFloorSubWord, if_pos h, ugt_one h]
    apply u256_inj
    rw [u256_mul_toNat]
    change (1 * (UInt256.sub x y).toNat) % UInt256.size = _
    rw [Nat.one_mul]
    exact Nat.mod_eq_of_lt (UInt256.sub x y).val.isLt
  · rw [zeroFloorSubWord, if_neg h, ugt_zero (Nat.le_of_not_gt h), u256_mul_zero_left]
    rfl

theorem zeroFloorSubWord_toNat (x y : UInt256) :
    (zeroFloorSubWord x y).toNat = x.toNat - y.toNat := by
  by_cases h : y.toNat < x.toNat
  · rw [zeroFloorSubWord, if_pos h, usub_toNat (Nat.le_of_lt h)]
  · rw [zeroFloorSubWord, if_neg h]; change 0 = x.toNat - y.toNat; omega

theorem evalZeroFloorSub {cfg : Config} {frame : Frame} {evm : EVM.State} {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg frame evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg frame evm ey = .ok (.int (Int.ofNat y.toNat))) :
    evalExpr? cfg frame evm (.ite (.binary .gt ex ey) (.binary .sub ex ey) (.intLit 0)) =
      .ok (.int (Int.ofNat (zeroFloorSubWord x y).toNat)) := by
  have hgt : evalExpr? cfg frame evm (.binary .gt ex ey) = .ok (.bool (decide (y.toNat < x.toNat))) := by
    rw [evalExpr_binary_nonshort (by decide) (by decide), hx, hy]
    simp only [bind, EvalResult.bind, evalBinaryOp?, Int.ofNat_eq_natCast, Int.ofNat_lt]
  by_cases h : y.toNat < x.toNat
  · rw [evalExpr?, hgt]
    simp only [decide_eq_true h, bind, EvalResult.bind]
    rw [subSourceOk hx hy (Nat.le_of_lt h), zeroFloorSubWord, if_pos h]
  · simp only [evalExpr?, hgt, decide_eq_false h, bind, EvalResult.bind, pure]
    rw [zeroFloorSubWord, if_neg h]
    rfl

def zeroFloorSubFrame (x y : UInt256) (imms : Store) : Frame := exactlyOneZeroFrame x y imms

theorem morphoZeroFloorSubBody (x y : UInt256) (evm : EVM.State) (imms : Store) :
    ExecFuncBody config (zeroFloorSubFrame x y imms) evm zeroFloorSubFunction.body
      (.returned (zeroFloorSubFrame x y imms) evm (some [.int (Int.ofNat (zeroFloorSubWord x y).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  apply ABlock.start.returns
  apply evalZeroFloorSub
  · simp only [evalExpr?, zeroFloorSubFrame, exactlyOneZeroFrame, store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, zeroFloorSubFrame, exactlyOneZeroFrame,
      store_get_ne _ _ (show ("x" == "y") = false by decide), store_get_self, EvalResult.ofOption]

theorem morphoZeroFloorSubCall (x y : UInt256) (evm : EVM.State) (locals imms : Store)
    (args : List Expr) (retVar : Ident)
    (he : evalExprs? config { contract := contract, locals := locals, immutables := imms } evm args =
      .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)]) :
    ExecStmt config { contract := contract, locals := locals, immutables := imms } evm
      (.internalCall "UtilsLib_zeroFloorSub" args retVar)
      (.ok { contract := contract, locals := locals.insert retVar (.int (Int.ofNat (zeroFloorSubWord x y).toNat)),
              immutables := imms } evm) :=
  internalCallFunctionReturn (callee := zeroFloorSubFunction) (value := some [.int (Int.ofNat (zeroFloorSubWord x y).toNat)])
    he rfl rfl (morphoZeroFloorSubBody x y evm imms)

end Benchmarks.Morpho.MorphoBlue
