import Examples.UniswapV2Pair.UpdateCouplingHelpers
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

theorem uniswapUpdateCallRevertsFirstBound
    {locals : Store} {args : List Expr} {retVar : Ident} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hargs : evalExprs? config { contract := contract, locals := locals } evm args =
      .ok (syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1))
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        args
        retVar) .reverted := by
  exact internalCallFunctionRevert
    (callee := updateFunction)
    (locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1)
    hargs
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call_with balance0 balance1 reserve0 reserve1)
    (uniswapUpdateFunctionReverts_firstBound_with evm balance0 balance1 reserve0 reserve1
      hbound)


theorem uniswapUpdateCallRevertsSecondBound
    {locals : Store} {args : List Expr} {retVar : Ident} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hargs : evalExprs? config { contract := contract, locals := locals } evm args =
      .ok (syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        args
        retVar) .reverted := by
  exact internalCallFunctionRevert
    (callee := updateFunction)
    (locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1)
    hargs
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call_with balance0 balance1 reserve0 reserve1)
    (uniswapUpdateFunctionReverts_secondBound_with evm balance0 balance1 reserve0 reserve1
      hbound0 hbound1)


theorem uniswapUpdateCallReturnsConditionTrue
    {locals : Store} {args : List Expr} {retVar : Ident} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hargs : evalExprs? config { contract := contract, locals := locals } evm args =
      .ok (syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0Ne : Int.ofNat reserve0.toNat ≠ 0)
    (hreserve1Ne : Int.ofNat reserve1.toNat ≠ 0) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        args
        retVar)
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          retVar none)
        (syncUpdateCumulativePackedReserveStateWith evm balance0 balance1 reserve0 reserve1)) := by
  have hbody :=
    uniswapUpdateFunctionReturns_conditionTrue_packed_with evm balance0 balance1 reserve0
      reserve1 hbound0 hbound1 helapsed hreserve0Ne hreserve1Ne
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := locals })
    (evm := evm)
    (calleeEvm := syncUpdateCumulativePackedReserveStateWith evm balance0 balance1 reserve0
      reserve1)
    (name := "_update") (retVar := retVar)
    (args := args)
    (argVals := syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1)
    (callee := updateFunction)
    (locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1)
    (calleeSolm :=
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 })
    (value := none)
    hargs
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call_with balance0 balance1 reserve0 reserve1)
    hbody


theorem uniswapUpdateCallReturnsConditionFalse
    {locals : Store} {args : List Expr} {retVar : Ident} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hargs : evalExprs? config { contract := contract, locals := locals } evm args =
      .ok (syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (hskip : syncTimeElapsedInt evm = 0 ∨ reserve0 = ⟨0⟩ ∨ reserve1 = ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        args
        retVar)
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          retVar none)
        (syncUpdatePackedReserveState evm balance0 balance1)) := by
  have hbody :=
    uniswapUpdateFunctionReturns_conditionFalse_packed_with evm balance0 balance1 reserve0
      reserve1
      hbound0 hbound1
      (evalExpr_sync_update_condition_false_with evm balance0 balance1 reserve0
        reserve1 hskip)
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := locals })
    (evm := evm)
    (calleeEvm := syncUpdatePackedReserveState evm balance0 balance1)
    (name := "_update") (retVar := retVar)
    (args := args)
    (argVals := syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1)
    (callee := updateFunction)
    (locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1)
    (calleeSolm :=
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 })
    (value := none)
    hargs
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call_with balance0 balance1 reserve0 reserve1)
    hbody


end UniswapV2Pair
