import Benchmarks.UniswapV4PoolManager.InitializeHookABI
import Benchmarks.UniswapV4PoolManager.HookWrapperSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev beforeInitializeFunction : FunctionDecl := contract.functions[33]!
abbrev afterInitializeFunction : FunctionDecl := contract.functions[34]!
theorem beforeInitialize_lookup : lookupCallable? contract "Hooks_beforeInitialize" =
    some beforeInitializeFunction.toCallable := rfl
theorem afterInitialize_lookup : lookupCallable? contract "Hooks_afterInitialize" =
    some afterInitializeFunction.toCallable := rfl

def poolKeyTupleExpr (e : Expr) : Expr := .tupleLit
  [.field e "currency0", .field e "currency1", .field e "fee", .field e "tickSpacing", .field e "hooks"]

theorem evalPoolKeyTuple {cfg : Config} {f : Frame} {evm : EVM.State} {e : Expr} {key : PoolKeyWords}
    (hk : evalExpr? cfg f evm e = .ok (poolKeyValue key)) :
    evalExpr? cfg f evm (poolKeyTupleExpr e) = .ok (.tuple (poolKeyValues key)) := by
  have h0 := evalStructField hk (field := "currency0") rfl
  have h1 := evalStructField hk (field := "currency1") rfl
  have h2 := evalStructField hk (field := "fee") rfl
  have h3 := evalStructField hk (field := "tickSpacing") rfl
  have h4 := evalStructField hk (field := "hooks") rfl
  rw [poolKeyTupleExpr, evalExpr?]
  simp only [evalExprList?, h0, h1, h2, h3, h4, bind, EvalResult.bind, pure]
  rfl

-- LIBRARY CANDIDATE: evaluated arguments and a configured ABI encoder determine a call payload.
theorem evalABIEncodeCall {cfg : Config} {f : Frame} {evm : EVM.State} {es : List Expr}
    {vs : List Value} {name : Ident} {data : ByteArray}
    (ha : evalExprList? cfg f evm es = .ok vs) (he : cfg.externalABI.encode? name vs = some data) :
    evalExpr? cfg f evm (.abiEncodeCall name es) = .ok (.bytes data) := by
  rw [evalExpr?, ha]
  simp only [bind, EvalResult.bind, he, EvalResult.ofOption, pure]

theorem beforeInitializeBody {f : Frame} {evm evm' : EVM.State} {hook : AccountAddress}
    {key : PoolKeyWords} {price : UInt256} {z : Bool} {out : ByteArray}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (hc : PoolKeyCanonical key) (hprice : price.toNat < 2^160)
    (hcall : hookEnabled evm.executionEnv.source hook ⟨8192⟩ →
      callViaEVM evm hook 0 (beforeInitializePayload evm.executionEnv.source key price) (z, evm', out)) :
    ∃ f', ExecFuncBody config f evm beforeInitializeFunction.body
      (hookInvocationResult f' evm evm' (hookEnabled evm.executionEnv.source hook ⟨8192⟩) z
        (beforeInitializePayload evm.executionEnv.source key price) out) := by
  have hcaller : evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
    simp only [evalExpr?, envValue, pure]
  have htuple := evalPoolKeyTuple (evalLocalValue (cfg := config) (evm := evm) hk)
  have hpriceExpr := evalLocalValue (cfg := config) (evm := evm) hp
  have hargs : evalExprList? config f evm [.env .caller, poolKeyTupleExpr (.var "key"), .var "sqrtPriceX96"] =
      .ok [.address evm.executionEnv.source, .tuple (poolKeyValues key), .int (Int.ofNat price.toNat)] := by
    simp only [evalExprList?, hcaller, htuple, hpriceExpr, bind, EvalResult.bind, pure]
  exact conditionalHookBody hf hs (hookEnabled_eval hs ⟨8192⟩ (by decide))
    (evalABIEncodeCall hargs (beforeInitializeEncode _ hc hprice))
    (by rw [beforeInitializePayload_size]; decide) hcall

theorem afterInitializeBody {f : Frame} {evm evm' : EVM.State} {hook : AccountAddress}
    {key : PoolKeyWords} {price tick : UInt256} {z : Bool} {out : ByteArray}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? "tick" = some (.int (EVM.signed tick)))
    (hc : PoolKeyCanonical key) (hprice : price.toNat < 2^160) (htick : int24Canonical tick)
    (hcall : hookEnabled evm.executionEnv.source hook ⟨4096⟩ →
      callViaEVM evm hook 0 (afterInitializePayload evm.executionEnv.source key price tick) (z, evm', out)) :
    ∃ f', ExecFuncBody config f evm afterInitializeFunction.body
      (hookInvocationResult f' evm evm' (hookEnabled evm.executionEnv.source hook ⟨4096⟩) z
        (afterInitializePayload evm.executionEnv.source key price tick) out) := by
  have hcaller : evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) := by
    simp only [evalExpr?, envValue, pure]
  have htuple := evalPoolKeyTuple (evalLocalValue (cfg := config) (evm := evm) hk)
  have hpriceExpr := evalLocalValue (cfg := config) (evm := evm) hp
  have htickExpr := evalLocalValue (cfg := config) (evm := evm) ht
  have hargs : evalExprList? config f evm
      [.env .caller, poolKeyTupleExpr (.var "key"), .var "sqrtPriceX96", .var "tick"] =
      .ok [.address evm.executionEnv.source, .tuple (poolKeyValues key), .int (Int.ofNat price.toNat),
        .int (EVM.signed tick)] := by
    simp only [evalExprList?, hcaller, htuple, hpriceExpr, htickExpr, bind, EvalResult.bind, pure]
  exact conditionalHookBody hf hs (hookEnabled_eval hs ⟨4096⟩ (by decide))
    (evalABIEncodeCall hargs (afterInitializeEncode _ hc hprice htick))
    (by rw [afterInitializePayload_size]; decide) hcall

end Benchmarks.UniswapV4PoolManager
