import Benchmarks.CurveVault.PriceArithmetic
import Benchmarks.CurveVault.ConversionFinishSource

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch
namespace Benchmarks.CurveVault

abbrev vaultPriceFinishBody : List Stmt := vaultPriceNonzeroBody.drop 4

def vaultPriceResultLocals (locals : Store) (isFloor : Bool) (value : UInt256) : Store :=
  (vaultConversionResultLocals (locals.insert "pps" (.int 0)) isFloor value).insert
    "pps" (.int (Int.ofNat value.toNat))

theorem vaultPriceRoundSource {evm : State} {locals : Store} {isFloor : Bool} {x y : UInt256}
    (hx : locals.get? "numerator" = some (.int (Int.ofNat x.toNat)))
    (hy : locals.get? "denominator" = some (.int (Int.ofNat y.toNat)))
    (hf : locals.get? "_is_floor" = some (.bool isFloor)) (hy0 : y ≠ ⟨0⟩) :
    ExecBlock fork config {contract := contract, locals := locals} evm (vaultPriceFinishBody.take 2)
      (.ok {contract := contract, locals := vaultPriceResultLocals locals isFloor (vaultConversionResult isFloor x y)} evm) := by
  let initial := locals.insert "pps" (.int 0)
  have hevalX := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show initial.get? "numerator" = some (.int (Int.ofNat x.toNat)) by
      rw [store_get_ne _ _ (by decide +kernel)]; exact hx)
  have hevalY := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show initial.get? "denominator" = some (.int (Int.ofNat y.toNat)) by
      rw [store_get_ne _ _ (by decide +kernel)]; exact hy)
  have hevalF : evalExpr? config {contract := contract, locals := initial} evm (.var "_is_floor") = .ok (.bool isFloor) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (initial.get? "_is_floor") = _
    rw [store_get_ne _ _ (by decide +kernel), hf]; rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp [evalExpr?, pure]))
  cases isFloor with
  | true =>
    refine ExecBlock.consNormal (ExecStmt.iteTrue hevalF ?_) ExecBlock.nil
    exact ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inl rfl) (evalExpr_div_uint256_ok hevalX hevalY hy0 rfl)
      (assignLocalVarBase_ok (old := .int 0) (by simp [initial]))) ExecBlock.nil
  | false =>
    have hcallee := vaultCeilDivSource (fork := fork) (evm := evm) (uintBinaryLocals_get_x x y) (uintBinaryLocals_get_y x y) hy0
    have hcall := internalCallFunctionReturn (caller := {contract := contract, locals := initial})
      (callee := vaultCeilDivFunction) (name := "math__ceil_div") (args := [.var "numerator", .var "denominator"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)]) (retVar := "__c1")
      (by simp [evalExprs?, hevalX, hevalY, bind, pure, EvalResult.bind]) rfl rfl hcallee
    refine ExecBlock.consNormal (ExecStmt.iteFalse hevalF ?_) ExecBlock.nil
    apply ExecBlock.consNormal hcall
    refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inl rfl) (value := .int (Int.ofNat (vaultCeilDivWord x y).toNat)) ?_ ?_) ExecBlock.nil
    · simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption, vaultConversionResult]
    · apply assignLocalVarBase_ok
      simp only [resumeAfterInternalCall, collapseReturns, initial, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      rfl

theorem vaultPriceFinishReturns {evm : State} {locals : Store} {isFloor : Bool} {x y : UInt256}
    (hx : locals.get? "numerator" = some (.int (Int.ofNat x.toNat)))
    (hy : locals.get? "denominator" = some (.int (Int.ofNat y.toNat)))
    (hf : locals.get? "_is_floor" = some (.bool isFloor)) (hy0 : y ≠ ⟨0⟩)
    (hvalue : vaultConversionResult isFloor x y ≠ ⟨0⟩) :
    ExecBlock fork config {contract := contract, locals := locals} evm vaultPriceFinishBody
      (.returned {contract := contract, locals := vaultPriceResultLocals locals isFloor (vaultConversionResult isFloor x y)}
        evm (some [.int (Int.ofNat (vaultConversionResult isFloor x y).toNat)])) := by
  have hbody : vaultPriceFinishBody = vaultPriceFinishBody.take 2 ++ vaultPriceFinishBody.drop 2 := rfl
  rw [hbody]
  apply execBlock_append (vaultPriceRoundSource hx hy hf hy0)
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show (vaultPriceResultLocals locals isFloor (vaultConversionResult isFloor x y)).get? "pps" =
      some (.int (Int.ofNat (vaultConversionResult isFloor x y).toNat)) by simp [vaultPriceResultLocals])
  have hpos : 0 < (vaultConversionResult isFloor x y).toNat := by
    have hn : (vaultConversionResult isFloor x y).toNat ≠ 0 := fun hz => hvalue (uint256_toNat_eq_zero hz)
    omega
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton heval)))
  rw [evalExpr?]
  simp only [heval, evalExpr?, evalBinaryOp?, bind, EvalResult.bind, pure]
  simp [hpos]
  all_goals decide +kernel

theorem vaultPriceFinishReverts {evm : State} {locals : Store} {isFloor : Bool} {x y : UInt256}
    (hx : locals.get? "numerator" = some (.int (Int.ofNat x.toNat)))
    (hy : locals.get? "denominator" = some (.int (Int.ofNat y.toNat)))
    (hf : locals.get? "_is_floor" = some (.bool isFloor)) (hy0 : y ≠ ⟨0⟩)
    (hvalue : vaultConversionResult isFloor x y = ⟨0⟩) :
    ExecBlock fork config {contract := contract, locals := locals} evm vaultPriceFinishBody .reverted := by
  have hbody : vaultPriceFinishBody = vaultPriceFinishBody.take 2 ++ vaultPriceFinishBody.drop 2 := rfl
  rw [hbody]
  apply execBlock_append (vaultPriceRoundSource hx hy hf hy0)
  have heval := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm)
    (show (vaultPriceResultLocals locals isFloor (vaultConversionResult isFloor x y)).get? "pps" =
      some (.int (Int.ofNat (vaultConversionResult isFloor x y).toNat)) by simp [vaultPriceResultLocals])
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  rw [evalExpr?]
  simp only [heval, evalExpr?, evalBinaryOp?, bind, EvalResult.bind, pure]
  rw [hvalue]
  rfl
  all_goals decide +kernel
end Benchmarks.CurveVault
