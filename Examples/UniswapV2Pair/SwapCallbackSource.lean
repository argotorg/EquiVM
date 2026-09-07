import Examples.UniswapV2Pair.SwapCallbackABI
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

abbrev swapCallbackCondition : Expr := .binary .gt (.arrayLength .localVar { base := "data" }) (.intLit 0)
abbrev swapCallbackBody : List Stmt := checkedExternalCallStmts (.var "to") "uniswapV2Call" (.intLit 0)
  [sender, .var "amount0Out", .var "amount1Out", .var "data"] "_callback"
abbrev swapCallbackStmt : Stmt := .ite swapCallbackCondition swapCallbackBody []
abbrev swapTransferPrefix : List Stmt := swapRecipientGuardPrefix ++ [swapFirstTransferStmt, swapSecondTransferStmt]
abbrev swapCallbackPrefix : List Stmt := swapTransferPrefix ++ [swapCallbackStmt]

theorem evalExpr_swap_callbackCondition {caller : Frame} (evm : EVM.State) (data : ByteArray)
    (hget : caller.locals.get? "data" = some (.bytes data)) :
    evalExpr? config caller evm swapCallbackCondition = .ok (.bool (decide (0 < data.size))) := by
  simp only [swapCallbackCondition, evalExpr?, hget, readLocalPath?, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]

theorem evalExprs_swap_callbackArgs {caller : Frame} (evm : EVM.State) (amount0Out amount1Out : UInt256) (data : ByteArray)
    (ha0 : caller.locals.get? "amount0Out" = some (uniswapUint256Value amount0Out))
    (ha1 : caller.locals.get? "amount1Out" = some (uniswapUint256Value amount1Out))
    (hdata : caller.locals.get? "data" = some (.bytes data)) :
    evalExprs? config caller evm [sender, .var "amount0Out", .var "amount1Out", .var "data"] =
      .ok (swapCallbackArgs evm.executionEnv.source amount0Out amount1Out data) := by
  simp only [evalExprs?, sender, evalExpr?, EvalResult.ofOption, ha0, ha1, hdata,
    EvalResult.bind, bind, pure, envValue]

theorem swapAfterTransfersFrame_get_ne (caller : Frame) (amount0Out amount1Out : UInt256) (key : Ident)
    (h0 : key ≠ "ok0") (h1 : key ≠ "ok1") :
    (swapAfterTransfersFrame caller amount0Out amount1Out).locals.get? key = caller.locals.get? key := by
  unfold swapAfterTransfersFrame
  rw [optionalSafeTransferFrame_get_ne _ _ _ _ h1, optionalSafeTransferFrame_get_ne _ _ _ _ h0]

theorem swapAfterTransfersFrame_data (evm : EVM.State) (I : ExecutionEnv) :
    (swapAfterTransfersFrame { contract := contract, locals := swapTokenStore evm I }
      (swapAmount0OutWord I) (swapAmount1OutWord I)).locals.get? "data" = some (swapDataValue I) := by
  rw [swapAfterTransfersFrame_get_ne _ _ _ _ (by decide) (by decide)]
  change (swapTokenStore evm I).get? "data" = _
  rw [swapTokenStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
    swapReserveStore, store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), swapStore_data]

theorem uniswapSwapCallbackSkip {caller : Frame} {evm : EVM.State}
    (hcond : evalExpr? config caller evm swapCallbackCondition = .ok (.bool false)) :
    ExecStmt config caller evm swapCallbackStmt (.ok caller evm) :=
  ExecStmt.iteFalse hcond ExecBlock.nil

theorem uniswapSwapCallbackNoCode {caller : Frame} {evm : EVM.State}
    (hcond : evalExpr? config caller evm swapCallbackCondition = .ok (.bool true))
    (hguard : evalExpr? config caller evm (.binary .gt (.extCodeSize (.var "to")) (.intLit 0)) = .ok (.bool false)) :
    ExecStmt config caller evm swapCallbackStmt .reverted :=
  ExecStmt.iteTrue hcond (checkedExternalCallNoCode hguard)

theorem uniswapSwapCallbackFailure {caller : Frame} {evm evm' : EVM.State} {recipient : AccountAddress}
    {argVals : List Value} {out : ByteArray}
    (hcond : evalExpr? config caller evm swapCallbackCondition = .ok (.bool true))
    (hguard : evalExpr? config caller evm (.binary .gt (.extCodeSize (.var "to")) (.intLit 0)) = .ok (.bool true))
    (hto : caller.locals.get? "to" = some (.address recipient))
    (hargs : evalExprs? config caller evm [sender, .var "amount0Out", .var "amount1Out", .var "data"] = .ok argVals)
    (hcall : typedCallViaEVM config evm (EVM.address recipient) "uniswapV2Call" 0 argVals (false, evm', out) true) :
    ExecStmt config caller evm swapCallbackStmt .reverted :=
  ExecStmt.iteTrue hcond (checkedExternalCallVarFailure hguard hto hargs hcall)

theorem uniswapSwapCallbackSuccess {caller : Frame} {evm evm' : EVM.State} {recipient : AccountAddress}
    {argVals : List Value} {out : ByteArray}
    (hcond : evalExpr? config caller evm swapCallbackCondition = .ok (.bool true))
    (hguard : evalExpr? config caller evm (.binary .gt (.extCodeSize (.var "to")) (.intLit 0)) = .ok (.bool true))
    (hto : caller.locals.get? "to" = some (.address recipient))
    (hargs : evalExprs? config caller evm [sender, .var "amount0Out", .var "amount1Out", .var "data"] = .ok argVals)
    (hcall : typedCallViaEVM config evm (EVM.address recipient) "uniswapV2Call" 0 argVals (true, evm', out) true) :
    ExecStmt config caller evm swapCallbackStmt
      (.ok { caller with locals := caller.locals.insert "_callback" (collapseReturns []) } evm') :=
  ExecStmt.iteTrue hcond (checkedExternalCallVarSuccess hguard hto hargs hcall rfl)

theorem uniswapSwapBodyReverts_callback (evm evmT : EVM.State) (I : ExecutionEnv) (caller : Frame)
    (hprefix : ExecBlock config { contract := contract, locals := swapStore I } evm swapTransferPrefix (.ok caller evmT))
    (hcallback : ExecStmt config caller evmT swapCallbackStmt .reverted) :
    ExecTransitionBody config contract evm (swapStore I) swapTransition.body .reverted := by
  exact ExecFuncBody.execBlockRevert (by
    simpa only [swapTransition, swapTransferPrefix, swapRecipientGuardPrefix, swapTokenPrefix, swapReserveGuardPrefix,
      swapReservePrefix, swapOutputPrefix, swapOutputRequireStmt, swapOutputRequireExpr,
      swapReserveRequireStmt, swapReserveRequireExpr, swapRecipientRequireStmt, swapRecipientRequireExpr,
      swapFirstTransferStmt, swapSecondTransferStmt, swapCallbackStmt, swapCallbackCondition, swapCallbackBody,
      List.append_assoc, List.cons_append, List.nil_append] using
      execBlock_append_term (execBlock_append hprefix (ExecBlock.consRevert hcallback)) (by intro f e h; cases h))

end UniswapV2Pair
