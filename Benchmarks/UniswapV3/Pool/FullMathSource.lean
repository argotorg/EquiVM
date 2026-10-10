import Benchmarks.UniswapV3.Pool.SourceWordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local instance] Classical.propDecidable

def fullMathProduct (a b : UInt256) : Nat := a.toNat * b.toNat

def fullMathValid (a b denominator : UInt256) : Prop :=
  fullMathProduct a b / UInt256.size < denominator.toNat

def fullMathResult (a b denominator : UInt256) : UInt256 :=
  UInt256.ofNat (fullMathProduct a b / denominator.toNat)

theorem fullMath_denominator_pos {a b denominator : UInt256}
    (h : fullMathValid a b denominator) : 0 < denominator.toNat := by
  exact Nat.lt_of_le_of_lt (Nat.zero_le _) h

theorem fullMath_quotient_lt {a b denominator : UInt256}
    (h : fullMathValid a b denominator) :
    fullMathProduct a b / denominator.toNat < UInt256.size := by
  have hd := fullMath_denominator_pos h
  have hp := (Nat.div_lt_iff_lt_mul (by decide : 0 < UInt256.size)).mp h
  apply (Nat.div_lt_iff_lt_mul hd).mpr
  simpa only [Nat.mul_comm] using hp

theorem fullMathResult_toNat {a b denominator : UInt256}
    (h : fullMathValid a b denominator) :
    (fullMathResult a b denominator).toNat = fullMathProduct a b / denominator.toNat :=
  UInt256.toNat_ofNat_of_lt (fullMath_quotient_lt h)

def fullMathFunction : FunctionDecl := contract.functions[22]!

theorem fullMathLookup :
    lookupCallable? contract "FullMath_mulDiv" = some fullMathFunction.toCallable := rfl

def fullMathLocals (a b denominator : UInt256) : Store :=
  (((∅ : Store).insert "denominator" (.int (Int.ofNat denominator.toNat))).insert "b"
    (.int (Int.ofNat b.toNat))).insert "a" (.int (Int.ofNat a.toNat))

def fullMathFrame (imms : Store) (a b denominator : UInt256) : Frame :=
  {contract := contract, locals := fullMathLocals a b denominator, immutables := imms}

theorem fullMathBind (a b denominator : UInt256) :
    bindParams? fullMathFunction.params [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat),
      .int (Int.ofNat denominator.toNat)] = some (fullMathLocals a b denominator) := rfl

def fullMathProductFrame (imms : Store) (a b denominator : UInt256) : Frame :=
  {fullMathFrame imms a b denominator with
    locals := (fullMathLocals a b denominator).insert "product"
      (.int (Int.ofNat (fullMathProduct a b)))}

theorem evalFullMathProduct (imms : Store) (evm : EVM.State) (a b denominator : UInt256) :
    evalExpr? config (fullMathFrame imms a b denominator) evm
      (.binary .mul (.var "a") (.var "b")) =
      .ok (.int (Int.ofNat (fullMathProduct a b))) := by
  simp [evalExpr?, fullMathFrame, fullMathLocals, fullMathProduct,
    Std.HashMap.getElem_insert, EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind]

theorem evalFullMathGuard (imms : Store) (evm : EVM.State) (a b denominator : UInt256) :
    evalExpr? config (fullMathProductFrame imms a b denominator) evm
      (.binary .gt (.var "denominator")
        (.binary .div (.var "product") (.binary .exp (.intLit 2) (.intLit 256)))) =
      .ok (.bool (decide (fullMathValid a b denominator))) := by
  simp [evalExpr?, fullMathProductFrame, fullMathFrame, fullMathLocals, fullMathValid,
    Std.HashMap.getElem_insert, EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind,
    UInt256.size]
  change (↑(fullMathProduct a b) / (↑UInt256.size : Int) < ↑denominator.toNat) ↔ _
  rw [← Int.natCast_ediv]
  exact Int.ofNat_lt

theorem fullMathReturns (imms : Store) (evm : EVM.State) (a b denominator : UInt256)
    (h : fullMathValid a b denominator) :
    ExecFuncBody config (fullMathFrame imms a b denominator) evm fullMathFunction.body
      (.returned (fullMathProductFrame imms a b denominator) evm
        (some [.int (Int.ofNat (fullMathResult a b denominator).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  refine ExecBlock.consNormal (solm' := fullMathProductFrame imms a b denominator)
    (evm' := evm) (ExecStmt.letDecl (evalFullMathProduct imms evm a b denominator)) ?_
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [h, decide_true] using evalFullMathGuard imms evm a b denominator
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have hd : denominator.toNat ≠ 0 := Nat.ne_of_gt (fullMath_denominator_pos h)
  simp [evalExprs?, evalExpr?, fullMathProductFrame, fullMathFrame, fullMathLocals,
    Std.HashMap.getElem_insert, EvalResult.ofOption, evalBinaryOp?, bind, EvalResult.bind,
    pure, hd, fullMathResult_toNat h, Int.natCast_ediv]

theorem fullMathReverts (imms : Store) (evm : EVM.State) (a b denominator : UInt256)
    (h : ¬ fullMathValid a b denominator) :
    ExecFuncBody config (fullMathFrame imms a b denominator) evm fullMathFunction.body
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  refine ExecBlock.consNormal (solm' := fullMathProductFrame imms a b denominator)
    (evm' := evm) (ExecStmt.letDecl (evalFullMathProduct imms evm a b denominator)) ?_
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [h, decide_false] using evalFullMathGuard imms evm a b denominator

end Benchmarks.UniswapV3.Pool
