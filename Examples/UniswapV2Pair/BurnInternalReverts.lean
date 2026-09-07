import Examples.UniswapV2Pair.BurnRoutines

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair


theorem evalExpr_burnFunction_balance_require_false (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256)
    (hlt : (burnFunctionFromBalanceWord evm holder).toNat < value.toNat) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterBalanceStore evm holder value } evm
      (.binary .ge (.var "fromBalance") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [burnFunctionAfterBalanceStore_fromBalance, burnFunctionAfterBalanceStore_value]
  simp [evalBinaryOp?, not_le.mpr hlt]

theorem evalExpr_burnFunction_totalSupply_require_false (evm : EVM.State)
    (holder : AccountAddress) (value : UInt256)
    (hlt : (burnFunctionTotalSupplyWord evm holder value).toNat < value.toNat) :
    evalExpr? config
      { contract := contract, locals := burnFunctionAfterTotalSupplyStore evm holder value }
      (burnFunctionAfterBalanceState evm holder value)
      (.binary .ge (.var "_totalSupply") (.var "value")) = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, EvalResult.bind, bind]
  rw [burnFunctionAfterTotalSupplyStore_totalSupplyLocal,
    burnFunctionAfterTotalSupplyStore_value]
  simp [evalBinaryOp?, not_le.mpr hlt]

theorem uniswapBurnFunctionBodyReverts_balanceUnderflow
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256)
    (hlt : (burnFunctionFromBalanceWord evm holder).toNat < value.toNat) :
    ExecFuncBody config { contract := contract, locals := burnFunctionCallStore holder value }
      evm burnFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config _ _ (_ :: _ :: _) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burnFunction_from_balance evm holder value)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse (evalExpr_burnFunction_balance_require_false evm holder value hlt))

theorem uniswapBurnFunctionBodyReverts_totalSupplyUnderflow
    (evm : EVM.State) (holder : AccountAddress) (value : UInt256)
    (hbalance : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat)
    (hlt : (burnFunctionTotalSupplyWord evm holder value).toNat < value.toNat) :
    ExecFuncBody config { contract := contract, locals := burnFunctionCallStore holder value }
      evm burnFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  change ExecBlock config _ _ (_ :: _ :: _ :: _ :: _ :: _) .reverted
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burnFunction_from_balance evm holder value)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.requireTrue
      (evalExpr_burnFunction_balance_require_true evm holder value hbalance)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (evalExpr_burnFunction_balance_debit evm holder value hbalance)
      (burnFunctionAssignBalance evm holder value)) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (evalExpr_burnFunction_totalSupply evm holder value)) ?_
  exact ExecBlock.consRevert
    (ExecStmt.requireFalse
      (evalExpr_burnFunction_totalSupply_require_false evm holder value hlt))

theorem uniswapBurnFunctionCallRevert_balanceUnderflow
    {caller : Frame} {evm : EVM.State} {holder : AccountAddress} {value : UInt256}
    {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [burnFunctionFromValue holder, burnFunctionValueValue value])
    (hlt : (burnFunctionFromBalanceWord evm holder).toNat < value.toNat) :
    ExecStmt config caller evm (.internalCall "_burn" args retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := caller) (evm := evm)
    (name := "_burn") (retVar := retVar) (args := args)
    (argVals := [burnFunctionFromValue holder, burnFunctionValueValue value])
    (callee := burnFunction) (locals := burnFunctionCallStore holder value)
    hargs (by simpa [hcontract] using uniswapLookupBurnFunction)
    (bindParams_burnFunction_call holder value)
    (by simpa [hcontract] using
      uniswapBurnFunctionBodyReverts_balanceUnderflow evm holder value hlt)

theorem uniswapBurnFunctionCallRevert_totalSupplyUnderflow
    {caller : Frame} {evm : EVM.State} {holder : AccountAddress} {value : UInt256}
    {args : List Expr} {retVar : Ident}
    (hcontract : caller.contract = contract)
    (hargs : evalExprs? config caller evm args =
      .ok [burnFunctionFromValue holder, burnFunctionValueValue value])
    (hbalance : value.toNat ≤ (burnFunctionFromBalanceWord evm holder).toNat)
    (hlt : (burnFunctionTotalSupplyWord evm holder value).toNat < value.toNat) :
    ExecStmt config caller evm (.internalCall "_burn" args retVar) .reverted := by
  exact internalCallFunctionRevert
    (cfg := config) (caller := caller) (evm := evm)
    (name := "_burn") (retVar := retVar) (args := args)
    (argVals := [burnFunctionFromValue holder, burnFunctionValueValue value])
    (callee := burnFunction) (locals := burnFunctionCallStore holder value)
    hargs (by simpa [hcontract] using uniswapLookupBurnFunction)
    (bindParams_burnFunction_call holder value)
    (by simpa [hcontract] using
      uniswapBurnFunctionBodyReverts_totalSupplyUnderflow evm holder value hbalance hlt)

end UniswapV2Pair
