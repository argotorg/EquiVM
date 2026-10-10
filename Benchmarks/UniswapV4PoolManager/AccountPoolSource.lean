import Benchmarks.UniswapV4PoolManager.AccountDeltaContinuation
import Benchmarks.UniswapV4PoolManager.BalanceDeltaComponentSource
import Benchmarks.UniswapV4PoolManager.PoolKeySource
import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev accountPoolFunction : FunctionDecl := contract.functions[19]!

def accountPoolCurrency (key : PoolKeyWords) (one : Bool) : AccountAddress :=
  AccountAddress.ofNat (if one then key.currency1 else key.currency0).toNat
def accountPoolComponentRet (one : Bool) : Ident := if one then "__c2" else "__c0"
def accountPoolAccountRet (one : Bool) : Ident := if one then "__c3" else "__c1"
def accountPoolStepFrame (f : Frame) (delta : UInt256) (one : Bool) : Frame :=
  {f with locals := f.locals.insert (accountPoolComponentRet one) (.int (balanceDeltaComponent one delta))}
def accountPoolStepResult (f : Frame) (evm : State) (key : PoolKeyWords)
    (delta : UInt256) (target : AccountAddress) (one : Bool) : ExecResult :=
  accountDeltaCallResult (accountPoolStepFrame f delta one) evm target (accountPoolCurrency key one)
    (balanceDeltaComponent one delta) (accountPoolAccountRet one)
def accountPoolStepStmts (one : Bool) : List Stmt :=
  [.internalCall (balanceDeltaComponentName one) [.var "delta"] (accountPoolComponentRet one),
   .internalCall "_accountDelta" [.field (.var "key") (if one then "currency1" else "currency0"),
     .var (accountPoolComponentRet one), .var "target"] (accountPoolAccountRet one)]

structure AccountPoolContext (f : Frame) (key : PoolKeyWords) (delta : UInt256) (target : AccountAddress) : Prop where
  contract : f.contract = Benchmarks.UniswapV4PoolManager.contract
  key : f.locals.get? "key" = some (poolKeyValue key)
  delta : f.locals.get? "delta" = some (.int (EVM.signed delta))
  target : f.locals.get? "target" = some (.address target)

theorem accountPoolStep {f : Frame} {evm : State} {key : PoolKeyWords}
    {delta : UInt256} {target : AccountAddress} (hc : AccountPoolContext f key delta target) (one : Bool) :
    ExecBlock config f evm (accountPoolStepStmts one) (accountPoolStepResult f evm key delta target one) := by
  have hgetter := balanceDeltaComponentCall hc.contract (evalLocalValue (evm := evm) hc.delta)
    one (accountPoolComponentRet one)
  have hk : (accountPoolStepFrame f delta one).locals.get? "key" = some (poolKeyValue key) := by
    exact (store_get_ne _ _ (by cases one <;> decide)).trans hc.key
  have ht : (accountPoolStepFrame f delta one).locals.get? "target" = some (.address target) := by
    exact (store_get_ne _ _ (by cases one <;> decide)).trans hc.target
  have hcurr := evalStructField (evalLocalValue (cfg := config) (evm := evm) hk)
    (field := if one then "currency1" else "currency0")
    (value := .address (accountPoolCurrency key one)) (by cases one <;> rfl)
  have haccount := accountDeltaCall (f := accountPoolStepFrame f delta one) hc.contract hcurr
    (evalLocalValue (store_get_self _ _ _)) (evalLocalValue ht) (accountPoolAccountRet one)
  exact ExecBlock.consNormal hgetter (execBlock_singleton haccount)

theorem accountPoolStepResult_context {f f' : Frame} {evm post : State} {key : PoolKeyWords}
    {delta : UInt256} {target : AccountAddress} {one : Bool}
    (hc : AccountPoolContext f key delta target)
    (h : accountPoolStepResult f evm key delta target one = .ok f' post) :
    AccountPoolContext f' key delta target := by
  obtain ⟨rfl, _⟩ := accountDeltaCallResult_normal h
  refine ⟨hc.contract, ?_, ?_, ?_⟩
  · exact (store_get_ne _ _ (by cases one <;> decide)).trans
      ((store_get_ne _ _ (by cases one <;> decide)).trans hc.key)
  · exact (store_get_ne _ _ (by cases one <;> decide)).trans
      ((store_get_ne _ _ (by cases one <;> decide)).trans hc.delta)
  · exact (store_get_ne _ _ (by cases one <;> decide)).trans
      ((store_get_ne _ _ (by cases one <;> decide)).trans hc.target)

def accountPoolBlockResult (f : Frame) (evm : State) (key : PoolKeyWords)
    (delta : UInt256) (target : AccountAddress) : ExecResult :=
  continueBlockResult (fun f1 post => accountPoolStepResult f1 post key delta target true)
    (accountPoolStepResult f evm key delta target false)
def accountPoolResult (f : Frame) (evm : State) (key : PoolKeyWords)
    (delta : UInt256) (target : AccountAddress) : ExecResult :=
  finishBlockResult (accountPoolBlockResult f evm key delta target)

theorem accountPoolBody {f : Frame} {evm : State} {key : PoolKeyWords}
    {delta : UInt256} {target : AccountAddress} (hc : AccountPoolContext f key delta target) :
    ExecFuncBody config f evm accountPoolFunction.body (accountPoolResult f evm key delta target) := by
  apply execFuncBody_block
  change ExecBlock config f evm (accountPoolStepStmts false ++ accountPoolStepStmts true) _
  apply execBlock_continue (accountPoolStep hc false)
  intro f1 post hh
  exact accountPoolStep (accountPoolStepResult_context hc hh) true

theorem accountPool_lookup : lookupCallable? contract "_accountPoolBalanceDelta" =
    some accountPoolFunction.toCallable := rfl

theorem accountPoolCall {f : Frame} {evm : State} {key : PoolKeyWords}
    {delta : UInt256} {target : AccountAddress} {ek ed et : Expr}
    (hf : f.contract = contract) (hk : evalExpr? config f evm ek = .ok (poolKeyValue key))
    (hd : evalExpr? config f evm ed = .ok (.int (EVM.signed delta)))
    (ht : evalExpr? config f evm et = .ok (.address target)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "_accountPoolBalanceDelta" [ek, ed, et] ret)
      (resumeCallResult f ret (accountPoolResult
        {f with locals := (((∅ : Store).insert "target" (.address target)).insert "delta"
          (.int (EVM.signed delta))).insert "key" (poolKeyValue key)} evm key delta target)) := by
  apply internalCallFunctionExec (argVals := [poolKeyValue key, .int (EVM.signed delta), .address target])
    (by simp only [evalExprs?, hk, hd, ht, bind, EvalResult.bind, pure])
    (by rw [hf]; exact accountPool_lookup) rfl
  exact accountPoolBody ⟨hf, store_get_self _ _ _,
    (store_get_ne _ _ (by decide)).trans (store_get_self _ _ _),
    (store_get_ne _ _ (by decide)).trans ((store_get_ne _ _ (by decide)).trans (store_get_self _ _ _))⟩

end Benchmarks.UniswapV4PoolManager
