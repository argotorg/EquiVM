import Benchmarks.Safe.SafeAddSource
import Benchmarks.Safe.WordExpressionSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeSubSource {cfg : Config} (caller : Frame) (evm : EVM.State) (a b : UInt256)
    (hfit : b.toNat ≤ a.toNat) :
    ExecFuncBody cfg (arithmeticFrame caller a b) evm subFunction.body
      (.returned (arithmeticFrame caller a b) evm (some [uint256Value (UInt256.sub a b)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  apply evalExprs?_singleton
  apply evalExpr_uint256_sub (a := a) (b := b) _ _ hfit <;>
    simp [evalExpr?, arithmeticFrame, arithmeticArgs, EvalResult.ofOption,
      Std.HashMap.getElem_insert]

theorem safeSubSourceUnderflow {cfg : Config} (caller : Frame) (evm : EVM.State)
    (a b : UInt256) (hlt : a.toNat < b.toNat) :
    ExecFuncBody cfg (arithmeticFrame caller a b) evm subFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  have he : evalExpr? cfg (arithmeticFrame caller a b) evm
      (sub256 (.var "x") (.var "y")) = .revert := by
    apply checkedSubSourceUnderflow (a := a) (b := b) _ _ hlt <;>
      simp [evalExpr?, arithmeticFrame, arithmeticArgs, EvalResult.ofOption,
        Std.HashMap.getElem_insert]
  simp [evalExprs?, he, bind, EvalResult.bind]

theorem safeInternalSub {caller : Frame} {evm : EVM.State} {lhs rhs : Expr}
    {a b : UInt256} {retVar : Ident} (hc : caller.contract = contract)
    (ha : evalExpr? config caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? config caller evm rhs = .ok (uint256Value b))
    (hfit : b.toNat ≤ a.toNat) :
    ExecStmt config caller evm (.internalCall "_sub" [lhs, rhs] retVar)
      (.ok { caller with
        locals := caller.locals.insert retVar (uint256Value (UInt256.sub a b)) } evm) := by
  apply internalCallFunctionReturn (callee := subFunction)
    (argVals := [uint256Value a, uint256Value b]) (locals := arithmeticArgs a b)
    (calleeSolm := arithmeticFrame caller a b) (value := some [uint256Value (UInt256.sub a b)])
  · simp [evalExprs?, ha, hb, bind, EvalResult.bind, pure]
  · rw [hc]; rfl
  · rfl
  · exact safeSubSource caller evm a b hfit

theorem safeInternalSubUnderflow {caller : Frame} {evm : EVM.State} {lhs rhs : Expr}
    {a b : UInt256} {retVar : Ident} (hc : caller.contract = contract)
    (ha : evalExpr? config caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? config caller evm rhs = .ok (uint256Value b))
    (hlt : a.toNat < b.toNat) :
    ExecStmt config caller evm (.internalCall "_sub" [lhs, rhs] retVar) .reverted := by
  apply internalCallFunctionRevert (callee := subFunction)
    (argVals := [uint256Value a, uint256Value b]) (locals := arithmeticArgs a b)
  · simp [evalExprs?, ha, hb, bind, EvalResult.bind, pure]
  · rw [hc]; rfl
  · rfl
  · exact safeSubSourceUnderflow caller evm a b hlt

end Benchmarks.Safe
