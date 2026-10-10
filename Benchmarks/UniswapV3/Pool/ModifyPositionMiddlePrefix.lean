import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem modifyPositionMiddlePrefixSource (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) :
    ExecBlock config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) (modifyPositionMiddleBody.take 2)
      (.ok (modifyPositionMiddleTimeFrame v a evm) (modifyPositionUpdatedState v a evm)) := by
  have hf : modifyPositionUpdatedFrame (immStore v) a evm =
      {contract := contract, locals := (modifyPositionUpdatedFrame (immStore v) a evm).locals,
        immutables := immStore v} := rfl
  have he := evalLiquidity (modifyPositionUpdatedFrame (immStore v) a evm).locals (immStore v)
    (modifyPositionUpdatedState v a evm) (by modify_position_updated_get)
  rw [← hf] at he
  have hli : ExecStmt config (modifyPositionUpdatedFrame (immStore v) a evm)
      (modifyPositionUpdatedState v a evm) modifyPositionMiddleBody[0]!
      (.ok (modifyPositionMiddleLiquidityFrame v a evm) (modifyPositionUpdatedState v a evm)) :=
    ExecStmt.letDecl he
  have hcall : ExecStmt config (modifyPositionMiddleLiquidityFrame v a evm)
      (modifyPositionUpdatedState v a evm) (.internalCall "_blockTimestamp" [] "__c6")
      (.ok (modifyPositionMiddleTimeFrame v a evm) (modifyPositionUpdatedState v a evm)) := by
    exact internalCallFunctionReturn (callee := blockTimestampFunction) (argVals := []) (locals := ∅)
      (calleeSolm := {contract := contract, locals := ∅, immutables := immStore v})
      (value := some [.int (Int.ofNat (modifyPositionMiddleOracleArgs v a evm).time.toNat)])
      (by rfl) blockTimestampLookup rfl (blockTimestampReturns (immStore v) _)
  exact ExecBlock.consNormal hli (ExecBlock.consNormal hcall ExecBlock.nil)

theorem evalModifyPositionMiddleOracleExprs (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm evm' : EVM.State) :
    evalExprs? config (modifyPositionMiddleTimeFrame v a evm) evm' modifyPositionMiddleOracleExprs =
      .ok [.int (Int.ofNat (modifyPositionMiddleOracleArgs v a evm).index.toNat),
        .int (Int.ofNat (modifyPositionMiddleOracleArgs v a evm).time.toNat),
        .int (modifyPositionMiddleOracleArgs v a evm).tick,
        .int (Int.ofNat (modifyPositionMiddleOracleArgs v a evm).liquidity.toNat),
        .int (Int.ofNat (modifyPositionMiddleOracleArgs v a evm).cardinality.toNat),
        .int (Int.ofNat (modifyPositionMiddleOracleArgs v a evm).cardinalityNext.toNat)] := by
  have hs : evalExpr? config (modifyPositionMiddleTimeFrame v a evm) evm' (.var "_slot0") =
      .ok (slot0StructValue evm.accountMap evm.executionEnv) :=
    evalExpr_var_get (by modify_position_middle_get)
  have hi := evalExpr_structField (name := "observationIndex") hs rfl
  have hk := evalExpr_structField (name := "tick") hs rfl
  have hc := evalExpr_structField (name := "observationCardinality") hs rfl
  have hn := evalExpr_structField (name := "observationCardinalityNext") hs rfl
  have ht : evalExpr? config (modifyPositionMiddleTimeFrame v a evm) evm' (.var "__c6") =
      .ok (.int (Int.ofNat (modifyPositionMiddleOracleArgs v a evm).time.toNat)) :=
    evalExpr_var_get (by modify_position_middle_get)
  have hl : evalExpr? config (modifyPositionMiddleTimeFrame v a evm) evm' (.var "liquidityBefore") =
      .ok (.int (Int.ofNat (modifyPositionMiddleLiquidity v a evm).toNat)) :=
    evalExpr_var_get (by modify_position_middle_get)
  simp only [modifyPositionMiddleOracleExprs, evalExprs?, hi, ht, hk, hl, hc, hn,
    modifyPositionMiddleOracleArgs, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
