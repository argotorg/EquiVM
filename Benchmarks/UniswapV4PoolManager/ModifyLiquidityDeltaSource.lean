import Benchmarks.UniswapV4PoolManager.BalanceDeltaCombineSource
import Benchmarks.UniswapV4PoolManager.ModifyLiquidityParams

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityDeltaFrame (f : Frame) (principal fees : UInt256) : Frame :=
  {f with locals :=
    let delta := .int (EVM.signed (balanceDeltaCombineWord false principal fees))
    (((f.locals.insert "principalDelta" (.int (EVM.signed principal))).insert
      "feesAccrued" (.int (EVM.signed fees))).insert "totalDelta" delta).insert "callerDelta" delta}

theorem modifyLiquidityDeltaSource {f : Frame} {evm : State} {principal fees : UInt256}
    {oldPrincipal oldFees oldCaller : Value} (hf : f.contract = contract)
    (ht : f.locals.get? "__c7" = some (.tuple [.int (EVM.signed principal), .int (EVM.signed fees)]))
    (hp : f.locals.get? "principalDelta" = some oldPrincipal)
    (he : f.locals.get? "feesAccrued" = some oldFees)
    (hc : f.locals.get? "callerDelta" = some oldCaller) :
    ExecBlock config f evm ((modifyLiquidityTransition.body.drop 20).take 4)
      (if balanceDeltaCombineFits false principal fees then
        .ok (modifyLiquidityDeltaFrame f principal fees) evm else .reverted) := by
  let f1 := {f with locals := f.locals.insert "principalDelta" (.int (EVM.signed principal))}
  let f2 := {f1 with locals := f1.locals.insert "feesAccrued" (.int (EVM.signed fees))}
  let f3 := {f2 with locals := f2.locals.insert "totalDelta" (.int (EVM.signed (balanceDeltaCombineWord false principal fees)))}
  have h1 : ExecStmt config f evm modifyLiquidityTransition.body[20]! (.ok f1 evm) :=
    ExecStmt.assign (evalTupleProjection (evalLocalValue ht) (i := 0) rfl) (assignLocalValue hp)
  have ht1 : f1.locals.get? "__c7" = some (.tuple [.int (EVM.signed principal), .int (EVM.signed fees)]) :=
    (store_get_ne _ _ (by decide : ("principalDelta" == "__c7") = false)).trans ht
  have he1 : f1.locals.get? "feesAccrued" = some oldFees :=
    (store_get_ne _ _ (by decide : ("principalDelta" == "feesAccrued") = false)).trans he
  have h2 : ExecStmt config f1 evm modifyLiquidityTransition.body[21]! (.ok f2 evm) :=
    ExecStmt.assign (evalTupleProjection (evalLocalValue ht1) (i := 1) rfl) (assignLocalValue he1)
  have hp2 : f2.locals.get? "principalDelta" = some (.int (EVM.signed principal)) :=
    (store_get_ne _ _ (by decide : ("feesAccrued" == "principalDelta") = false)).trans (store_get_self _ _ _)
  have he2 : f2.locals.get? "feesAccrued" = some (.int (EVM.signed fees)) := store_get_self _ _ _
  have hf2 : f2.contract = contract := hf
  have h3 := balanceDeltaCombineCall hf2 (evalLocalValue (evm := evm) hp2)
    (evalLocalValue he2) false "totalDelta"
  by_cases hfit : balanceDeltaCombineFits false principal fees
  · rw [if_pos hfit] at h3 ⊢
    have hc3 : f3.locals.get? "callerDelta" = some oldCaller :=
      (store_get_ne3 _ _ _ _ (by decide : ("principalDelta" == "callerDelta") = false)
        (by decide : ("feesAccrued" == "callerDelta") = false)
        (by decide : ("totalDelta" == "callerDelta") = false)).trans hc
    exact ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (ExecBlock.consNormal h3
      (execBlock_singleton (ExecStmt.assign (evalLocalValue (store_get_self _ _ _)) (assignLocalValue hc3)))))
  · rw [if_neg hfit] at h3 ⊢
    exact ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (ExecBlock.consRevert h3))

theorem modifyLiquidityEmitSource {f : Frame} {evm : State} {id : UInt256} {p : ModifyLiquidityWords}
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p)) :
    ExecStmt config f evm modifyLiquidityTransition.body[24]! (.ok f evm) := by
  have hparams := evalLocalValue (cfg := config) (evm := evm) hp
  have hlo := evalStructField hparams (field := "tickLower") rfl
  have hup := evalStructField hparams (field := "tickUpper") rfl
  have hdelta := evalStructField hparams (field := "liquidityDelta") rfl
  have hsalt := evalStructField hparams (field := "salt") rfl
  apply ExecStmt.emit (vals := [wordBytes32Value id,
    .address evm.executionEnv.source, .int (EVM.signed p.lower), .int (EVM.signed p.upper),
    .int (EVM.signed p.delta), wordBytes32Value p.salt])
  change evalExprs? config f evm [.var "id", .env .caller, .field (.var "params") "tickLower",
    .field (.var "params") "tickUpper", .field (.var "params") "liquidityDelta", .field (.var "params") "salt"] = _
  simp only [evalExprs?, evalLocalValue hi, hlo, hup, hdelta, hsalt, evalExpr?, envValue,
    bind, EvalResult.bind, pure]

theorem modifyLiquidityEventSource {f : Frame} {evm : State} {id : UInt256} {p : ModifyLiquidityWords}
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p)) :
    ExecBlock config f evm ((modifyLiquidityTransition.body.drop 24).take 2)
      (.ok {f with locals := f.locals.insert "hookDelta" (.int 0)} evm) :=
  ExecBlock.consNormal (modifyLiquidityEmitSource hi hp)
    (execBlock_singleton (ExecStmt.letDecl (by simp only [evalExpr?, pure])))

theorem modifyLiquidityEventStaticSource {f : Frame} {evm : State} {id : UInt256} {p : ModifyLiquidityWords}
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config f evm ((modifyLiquidityTransition.body.drop 24).take 2) .staticViolation := by
  have hs := modifyLiquidityEmitSource (evm := evm) hi hp
  cases hs with
  | emit he => exact ExecBlock.consStatic (ExecStmt.emitStatic he hperm)

end Benchmarks.UniswapV4PoolManager
