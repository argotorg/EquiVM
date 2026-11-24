import Benchmarks.CurveVault.ConvertSharesArithmetic

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.VyperDispatch Reasoning.VyperCalls
namespace Benchmarks.CurveVault


abbrev vaultConversionFinishBody : List Stmt := vaultConvertSharesFunction.body.drop 5

def vaultConversionResult (isFloor : Bool) (numerator denominator : UInt256) : UInt256 :=
  if isFloor then UInt256.div numerator denominator else vaultCeilDivWord numerator denominator

def vaultConversionResultLocals (locals : Store) (isFloor : Bool) (value : UInt256) : Store :=
  if isFloor then locals else locals.insert "__c1" (.int (Int.ofNat value.toNat))

theorem vaultConversionFinishReturns {evm : State} {locals : Store} {isFloor : Bool} {x y : UInt256}
    (hx : locals.get? "numerator" = some (.int (Int.ofNat x.toNat)))
    (hy : locals.get? "denominator" = some (.int (Int.ofNat y.toNat)))
    (hf : locals.get? "_is_floor" = some (.bool isFloor)) (hy0 : y ≠ ⟨0⟩) :
    ExecBlock fork config {contract := contract, locals := locals} evm vaultConversionFinishBody
      (.returned {contract := contract, locals :=
        vaultConversionResultLocals locals isFloor (vaultConversionResult isFloor x y)}
        evm (some [.int (Int.ofNat (vaultConversionResult isFloor x y).toNat)])) := by
  have hevalX := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hx
  have hevalY := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hy
  have hevalF : evalExpr? config {contract := contract, locals := locals} evm (.var "_is_floor") = .ok (.bool isFloor) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "_is_floor") = _
    rw [hf]; rfl
  cases isFloor with
  | true =>
    apply ExecBlock.consReturn (ExecStmt.iteTrue hevalF ?_)
    exact ExecBlock.consReturn (ExecStmt.return
      (evalExprs?_singleton (evalExpr_div_uint256_ok hevalX hevalY hy0 rfl)))
  | false =>
    apply ExecBlock.consReturn (ExecStmt.iteFalse hevalF ?_)
    have hcallee := vaultCeilDivSource (fork := fork) (evm := evm)
      (uintBinaryLocals_get_x x y) (uintBinaryLocals_get_y x y) hy0
    have hcall := internalCallFunctionReturn
      (caller := {contract := contract, locals := locals}) (callee := vaultCeilDivFunction)
      (name := "math__ceil_div") (args := [.var "numerator", .var "denominator"])
      (argVals := [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)]) (retVar := "__c1")
      (by simp [evalExprs?, hevalX, hevalY, bind, pure, EvalResult.bind]) rfl rfl hcallee
    apply ExecBlock.consNormal hcall
    exact ExecBlock.consReturn (ExecStmt.return (evalExprs?_singleton (by
      simp [resumeAfterInternalCall, collapseReturns, evalExpr?, EvalResult.ofOption, vaultConversionResult])))

theorem vaultConversionFinishReverts {evm : State} {locals : Store} {isFloor : Bool} {x : UInt256}
    (hx : locals.get? "numerator" = some (.int (Int.ofNat x.toNat)))
    (hy : locals.get? "denominator" = some (.int 0))
    (hf : locals.get? "_is_floor" = some (.bool isFloor)) :
    ExecBlock fork config {contract := contract, locals := locals} evm vaultConversionFinishBody .reverted := by
  have hevalX := evalExpr_varUInt256 (cfg := config) (contract := contract) (evm := evm) hx
  have hevalY := evalExpr_varInt (cfg := config) (contract := contract) (evm := evm) hy
  have hevalF : evalExpr? config {contract := contract, locals := locals} evm (.var "_is_floor") = .ok (.bool isFloor) := by
    rw [evalExpr?]
    change EvalResult.ofOption EvalError.unboundVariable (locals.get? "_is_floor") = _
    rw [hf]; rfl
  cases isFloor with
  | true =>
    apply ExecBlock.consRevert (ExecStmt.iteTrue hevalF ?_)
    apply ExecBlock.consRevert (ExecStmt.returnRevert ?_)
    simp [evalExprs?, evalExpr?, hevalX, hevalY, evalBinaryOp?, bind, EvalResult.bind]
  | false =>
    have hcallee := vaultCeilDivSourceRevert (fork := fork) (evm := evm) (uintBinaryLocals_get_y x ⟨0⟩)
    apply ExecBlock.consRevert (ExecStmt.iteFalse hevalF ?_)
    exact ExecBlock.consRevert (internalCallFunctionRevert
      (caller := {contract := contract, locals := locals}) (callee := vaultCeilDivFunction)
      (args := [.var "numerator", .var "denominator"])
      (argVals := [.int (Int.ofNat x.toNat), .int 0])
      (by simp [evalExprs?, hevalX, hevalY, bind, pure, EvalResult.bind]) rfl rfl hcallee)
end Benchmarks.CurveVault
