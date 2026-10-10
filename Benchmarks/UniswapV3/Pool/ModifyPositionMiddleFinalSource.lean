import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleAmountsModel
import Benchmarks.UniswapV3.Pool.PoolLiquidityStore
import Benchmarks.UniswapV3.Pool.LiquidityDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState

def modifyPositionMiddleNewLiquidity (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : Int :=
  liquidityDeltaResult (Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat) a.delta

noncomputable def modifyPositionMiddleFinalFrame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (modifyPositionMiddleAssigned1Frame v a evm) "__c12"
    (some [.int (modifyPositionMiddleNewLiquidity v a evm)])

def modifyPositionMiddleFinalState (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : EVM.State :=
  storePoolLiquidity (modifyPositionMiddleStoresState v a evm)
    (EVM.wordOfInt (modifyPositionMiddleNewLiquidity v a evm))

def modifyPositionMiddleDeltaExprs : List Expr :=
  [.var "liquidityBefore", .field (.var "params") "liquidityDelta"]

macro "modify_position_middle_final_get" : tactic =>
  `(tactic| (simp only [modifyPositionMiddleFinalFrame, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; modify_position_middle_amount_get))

theorem evalModifyPositionMiddleDeltaExprs (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm evm' : EVM.State) :
    evalExprs? config (modifyPositionMiddleAssigned1Frame v a evm) evm' modifyPositionMiddleDeltaExprs =
      .ok [.int (Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat), .int a.delta] := by
  have hl : evalExpr? config (modifyPositionMiddleAssigned1Frame v a evm) evm' (.var "liquidityBefore") =
      .ok (.int (Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat)) :=
    evalExpr_var_get (by modify_position_middle_amount_get)
  have hp : evalExpr? config (modifyPositionMiddleAssigned1Frame v a evm) evm' (.var "params") =
      .ok a.value := evalExpr_var_get (by modify_position_middle_amount_get)
  have hd := evalExpr_structField (name := "liquidityDelta") hp rfl
  simp only [modifyPositionMiddleDeltaExprs, evalExprs?, hl, hd, bind, EvalResult.bind, pure]

theorem modifyPositionMiddleLiquidityStoreSource (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm evm' : EVM.State) :
    ExecStmt config (modifyPositionMiddleFinalFrame v a evm) evm'
      (.assign .storage ⟨"liquidity", []⟩ (.var "__c12"))
      (.ok (modifyPositionMiddleFinalFrame v a evm)
        (storePoolLiquidity evm' (EVM.wordOfInt (modifyPositionMiddleNewLiquidity v a evm)))) := by
  have hf : modifyPositionMiddleFinalFrame v a evm =
      {contract := contract, locals := (modifyPositionMiddleFinalFrame v a evm).locals,
        immutables := immStore v} := rfl
  have hs := assignPoolLiquidity (modifyPositionMiddleFinalFrame v a evm).locals (immStore v) evm'
    (modifyPositionMiddleNewLiquidity v a evm) (by modify_position_middle_final_get)
  rw [← hf] at hs
  exact ExecStmt.assign (evalExpr_var_get (by modify_position_middle_final_get)) hs

theorem modifyPositionMiddleReturnSource (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm evm' : EVM.State) :
    ExecStmt config (modifyPositionMiddleFinalFrame v a evm) evm'
      (.return [.var "position", .var "amount0", .var "amount1"])
      (.returned (modifyPositionMiddleFinalFrame v a evm) evm'
        (some [modifyPositionKeyValue a,
          .int (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false)),
          .int (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true))])) := by
  have hk : evalExpr? config (modifyPositionMiddleFinalFrame v a evm) evm' (.var "position") =
      .ok (modifyPositionKeyValue a) := evalExpr_var_get (by modify_position_middle_final_get)
  have h0 : evalExpr? config (modifyPositionMiddleFinalFrame v a evm) evm' (.var "amount0") =
      .ok (.int (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false))) :=
    evalExpr_var_get (by modify_position_middle_final_get)
  have h1 : evalExpr? config (modifyPositionMiddleFinalFrame v a evm) evm' (.var "amount1") =
      .ok (.int (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true))) :=
    evalExpr_var_get (by modify_position_middle_final_get)
  exact ExecStmt.return (by simp only [evalExprs?, hk, h0, h1, bind, EvalResult.bind, pure])

end Benchmarks.UniswapV3.Pool
