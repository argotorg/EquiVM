import Benchmarks.Safe.SafeAddSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeMulSource {cfg : Config} (caller : Frame) (evm : EVM.State) (a b : UInt256)
    (hfit : a.toNat * b.toNat < UInt256.size) :
    ExecFuncBody cfg (arithmeticFrame caller a b) evm mulFunction.body
      (.returned (arithmeticFrame caller a b) evm (some [uint256Value (UInt256.mul a b)])) := by
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consReturn
  apply ExecStmt.return
  apply evalExprs?_singleton
  apply checkedMulSourceOk (a := a) (b := b) _ _ hfit <;>
    simp [evalExpr?, arithmeticFrame, arithmeticArgs, EvalResult.ofOption,
      Std.HashMap.getElem_insert]

theorem safeMulSourceOverflow {cfg : Config} (caller : Frame) (evm : EVM.State)
    (a b : UInt256) (hover : UInt256.size ≤ a.toNat * b.toNat) :
    ExecFuncBody cfg (arithmeticFrame caller a b) evm mulFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply ExecBlock.consRevert
  apply ExecStmt.returnRevert
  have he : evalExpr? cfg (arithmeticFrame caller a b) evm
      (mul256 (.var "x") (.var "y")) = .revert := by
    apply checkedMulSourceOverflow (a := a) (b := b) _ _ hover <;>
      simp [evalExpr?, arithmeticFrame, arithmeticArgs, EvalResult.ofOption,
        Std.HashMap.getElem_insert]
  simp [evalExprs?, he, bind, EvalResult.bind]

theorem safeInternalMul {caller : Frame} {evm : EVM.State} {lhs rhs : Expr}
    {a b : UInt256} {retVar : Ident} (hc : caller.contract = contract)
    (ha : evalExpr? config caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? config caller evm rhs = .ok (uint256Value b))
    (hfit : a.toNat * b.toNat < UInt256.size) :
    ExecStmt config caller evm (.internalCall "_mul" [lhs, rhs] retVar)
      (.ok { caller with locals := caller.locals.insert retVar (uint256Value (UInt256.mul a b)) }
        evm) := by
  apply internalCallFunctionReturn (callee := mulFunction)
    (argVals := [uint256Value a, uint256Value b]) (locals := arithmeticArgs a b)
    (calleeSolm := arithmeticFrame caller a b) (value := some [uint256Value (UInt256.mul a b)])
  · simp [evalExprs?, ha, hb, bind, EvalResult.bind, pure]
  · rw [hc]
    rfl
  · rfl
  · exact safeMulSource caller evm a b hfit

theorem safeInternalMulOverflow {caller : Frame} {evm : EVM.State} {lhs rhs : Expr}
    {a b : UInt256} {retVar : Ident} (hc : caller.contract = contract)
    (ha : evalExpr? config caller evm lhs = .ok (uint256Value a))
    (hb : evalExpr? config caller evm rhs = .ok (uint256Value b))
    (hover : UInt256.size ≤ a.toNat * b.toNat) :
    ExecStmt config caller evm (.internalCall "_mul" [lhs, rhs] retVar) .reverted := by
  apply internalCallFunctionRevert (callee := mulFunction)
    (argVals := [uint256Value a, uint256Value b]) (locals := arithmeticArgs a b)
  · simp [evalExprs?, ha, hb, bind, EvalResult.bind, pure]
  · rw [hc]
    rfl
  · rfl
  · exact safeMulSourceOverflow caller evm a b hover

end Benchmarks.Safe
