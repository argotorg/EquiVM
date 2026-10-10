import Benchmarks.UniswapV4PoolManager.SwapAfterSource
import Benchmarks.UniswapV4PoolManager.PoolSwapValues
import Benchmarks.UniswapV4PoolManager.PoolStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapPoolParams (key : PoolKeyWords) (p : SwapParamsWords) (amount fee : UInt256) : PoolSwapParamsWords :=
  ⟨amount, key.tickSpacing, p.zeroForOne, p.priceLimit, fee⟩

def swapPoolCurrency (key : PoolKeyWords) (p : SwapParamsWords) : AccountAddress :=
  AccountAddress.ofNat (if p.zeroForOne then key.currency0 else key.currency1).toNat

def swapPoolParamsExpr : Expr := .structLit "Pool_SwapParams"
  [("tickSpacing", .field (.var "key") "tickSpacing"),
   ("zeroForOne", .field (.var "params") "zeroForOne"), ("amountSpecified", .var "amountToSwap"),
   ("sqrtPriceLimitX96", .field (.var "params") "sqrtPriceLimitX96"), ("lpFeeOverride", .var "lpFeeOverride")]

def swapPoolCurrencyExpr : Expr := .ite (.field (.var "params") "zeroForOne")
  (.field (.var "key") "currency0") (.field (.var "key") "currency1")

theorem swapPoolParams_eval {f : Frame} {evm : State} {key : PoolKeyWords}
    {p : SwapParamsWords} {amount fee : UInt256}
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hf : f.locals.get? "lpFeeOverride" = some (.int (Int.ofNat fee.toNat))) :
    evalExpr? config f evm swapPoolParamsExpr = .ok (poolSwapParamsValue (swapPoolParams key p amount fee)) := by
  have hekey := evalLocalValue (cfg := config) (evm := evm) hk
  have heparams := evalLocalValue (cfg := config) (evm := evm) hp
  have hs := evalStructField hekey (field := "tickSpacing") rfl
  have hz := evalStructField heparams (field := "zeroForOne") rfl
  have hl := evalStructField heparams (field := "sqrtPriceLimitX96") rfl
  have heamount := evalLocalValue (cfg := config) (evm := evm) ha
  have hefee := evalLocalValue (cfg := config) (evm := evm) hf
  simp only [swapPoolParamsExpr, evalExpr?, evalStructFields?, hs, hz, hl, heamount, hefee,
    bind, EvalResult.bind, pure]
  rfl

theorem swapPoolCurrency_eval {f : Frame} {evm : State} {key : PoolKeyWords} {p : SwapParamsWords}
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p)) :
    evalExpr? config f evm swapPoolCurrencyExpr = .ok (.address (swapPoolCurrency key p)) := by
  have hekey := evalLocalValue (cfg := config) (evm := evm) hk
  have hz := evalStructField (evalLocalValue (cfg := config) (evm := evm) hp) (field := "zeroForOne") rfl
  have h0 := evalStructField hekey (field := "currency0") rfl
  have h1 := evalStructField hekey (field := "currency1") rfl
  cases hd : p.zeroForOne <;>
    simp only [swapPoolCurrencyExpr, evalExpr?, hz, hd, bind, EvalResult.bind, Bool.false_eq_true,
      if_false, if_true, h0, h1, swapPoolCurrency]

def swapPoolAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.28"
def swapPoolAliasFrame (f : Frame) (id : UInt256) : Frame :=
  {f with locals := f.locals.insert swapPoolAlias (poolRefValue id)}
def swapPoolCallFrame (f : Frame) (delta : UInt256) : Frame :=
  {f with locals := f.locals.insert "__c6" (.int (EVM.signed delta))}
def swapPoolDeltaFrame (f : Frame) (delta : UInt256) : Frame :=
  { (swapPoolCallFrame f delta) with locals := (swapPoolCallFrame f delta).locals.insert "swapDelta" (.int (EVM.signed delta)) }

theorem swapPoolAliasSource {f : Frame} {evm : State} {id : UInt256}
    (hp : f.locals.get? "pool" = some (poolRefValue id)) :
    ExecStmt config f evm swapTransition.body[22]! (.ok (swapPoolAliasFrame f id) evm) :=
  ExecStmt.letStorage (resolveStorageAlias hp)

theorem swapPoolDeltaSource {f : Frame} {evm : State} {delta : UInt256} {old : Value}
    (hd : f.locals.get? "swapDelta" = some old) :
    ExecStmt config (swapPoolCallFrame f delta) evm swapTransition.body[24]!
      (.ok (swapPoolDeltaFrame f delta) evm) :=
  ExecStmt.assign (evalLocalValue (store_get_self _ _ _))
    (assignLocalValue ((store_get_ne _ _ (by decide : ("__c6" == "swapDelta") = false)).trans hd))

end Benchmarks.UniswapV4PoolManager
