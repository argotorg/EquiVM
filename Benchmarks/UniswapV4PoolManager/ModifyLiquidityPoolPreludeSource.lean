import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams
import Benchmarks.UniswapV4PoolManager.PoolModifyValues
import Benchmarks.UniswapV4PoolManager.PoolStorage
import Benchmarks.UniswapV4PoolManager.SafeCast128Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityPoolParams (sender : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) : PoolModifyParams :=
  ⟨sender, p.lower, p.upper, EVM.signed p.delta, key.tickSpacing, p.salt⟩

def modifyLiquidityPoolParamsExpr : Expr := .structLit "Pool_ModifyLiquidityParams"
  [("owner", .env .caller), ("tickLower", .field (.var "params") "tickLower"),
   ("tickUpper", .field (.var "params") "tickUpper"), ("liquidityDelta", .var "__c6"),
   ("tickSpacing", .field (.var "key") "tickSpacing"), ("salt", .field (.var "params") "salt")]

theorem modifyLiquidityPoolParams_eval {f : Frame} {evm : State} {key : PoolKeyWords}
    {p : ModifyLiquidityWords} (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hd : f.locals.get? "__c6" = some (.int (EVM.signed p.delta))) :
    evalExpr? config f evm modifyLiquidityPoolParamsExpr =
      .ok (poolModifyParamsValue (modifyLiquidityPoolParams evm.executionEnv.source key p)) := by
  have hk' := evalLocalValue (cfg := config) (evm := evm) hk
  have hp' := evalLocalValue (cfg := config) (evm := evm) hp
  have hl := evalStructField hp' (field := "tickLower") rfl
  have hu := evalStructField hp' (field := "tickUpper") rfl
  have hs := evalStructField hp' (field := "salt") rfl
  have ht := evalStructField hk' (field := "tickSpacing") rfl
  have hdelta := evalLocalValue (cfg := config) (evm := evm) hd
  simp only [modifyLiquidityPoolParamsExpr, evalExpr?, evalStructFields?, hl, hu, hs, ht, hdelta,
    envValue, bind, EvalResult.bind, pure]
  rfl

def modifyLiquidityPoolAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.25"
def modifyLiquidityPoolPreludeFrame (f : Frame) (id : UInt256) (p : ModifyLiquidityWords) : Frame :=
  {f with locals := ((f.locals.insert "principalDelta" (.int 0)).insert
    "__c6" (.int (EVM.signed p.delta))).insert modifyLiquidityPoolAlias (poolRefValue id)}

theorem modifyLiquidityPoolPreludeSource {f : Frame} {evm : State} {id : UInt256}
    {p : ModifyLiquidityWords} (hf : f.contract = contract)
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hs : f.locals.get? "pool" = some (poolRefValue id)) :
    ExecBlock config f evm ((modifyLiquidityTransition.body.drop 16).take 3)
      (if signedFits ⟨128, by decide⟩ (EVM.signed p.delta) then
        .ok (modifyLiquidityPoolPreludeFrame f id p) evm else .reverted) := by
  let f1 : Frame := {f with locals := f.locals.insert "principalDelta" (.int 0)}
  have hzero : ExecStmt config f evm modifyLiquidityTransition.body[16]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure])
  have hparams := evalLocalValue (cfg := config) (f := f1) (evm := evm)
    ((store_get_ne _ _ (by decide : ("principalDelta" == "params") = false)).trans hp)
  have hf1 : f1.contract = contract := hf
  have hcast := signedToInt128Call hf1 (evalStructField hparams (field := "liquidityDelta") rfl) "__c6"
  by_cases hd : signedFits ⟨128, by decide⟩ (EVM.signed p.delta)
  · rw [if_pos hd] at hcast ⊢
    exact ExecBlock.consNormal hzero (ExecBlock.consNormal hcast
      (execBlock_singleton (ExecStmt.letStorage (resolveStorageAlias
        ((store_get_ne2 _ _ _ (by decide : ("principalDelta" == "pool") = false)
          (by decide : ("__c6" == "pool") = false)).trans hs)))))
  · rw [if_neg hd] at hcast ⊢
    exact ExecBlock.consNormal hzero (ExecBlock.consRevert hcast)

end Benchmarks.UniswapV4PoolManager
