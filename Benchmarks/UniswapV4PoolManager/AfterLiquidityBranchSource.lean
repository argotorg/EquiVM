import Benchmarks.UniswapV4PoolManager.AfterLiquidityFinishSource
import Benchmarks.UniswapV4PoolManager.HookDeltaSource
import Benchmarks.UniswapV4PoolManager.LiquidityHookSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev afterLiquidityFunction : FunctionDecl := contract.functions[36]!
def afterLiquidityFlag (add : Bool) : UInt256 := if add then ⟨1024⟩ else ⟨256⟩
def afterLiquidityDeltaFlag (add : Bool) : UInt256 := if add then ⟨2⟩ else ⟨1⟩
def afterLiquidityParse (hook : AccountAddress) (add : Bool) : Bool :=
  decide (UInt256.land (accountWord hook) (afterLiquidityDeltaFlag add) ≠ ⟨0⟩)
def afterLiquidityPayloadExpr (add : Bool) : Expr :=
  liquidityHookPayloadExpr true add (.env .caller) (.var "key") (.var "params") (.var "delta")
    (.var "feesAccrued") (.var "hookData")
def afterLiquidityPayload (add : Bool) (sender : AccountAddress) (key : PoolKeyWords)
    (p : ModifyLiquidityWords) (delta fees : UInt256) (data : ByteArray) : ByteArray :=
  liquidityHookPayload true add sender key p delta fees data
def afterLiquidityBranch (add : Bool) : List Stmt :=
  [.letDecl "payload" (some .bytes) (afterLiquidityPayloadExpr add),
   .internalCall "Hooks_callHookWithReturnDelta" [.var "self", .var "payload",
     hookPermissionExpr (.var "self") (afterLiquidityDeltaFlag add)] "result"] ++ afterLiquidityFinishStmts
def afterLiquidityReplyFrame (f : Frame) (payload out : ByteArray) (parse : Bool) : Frame :=
  let locals := f.locals.insert "payload" (.bytes payload)
  {f with locals := locals.insert "result" (.int (EVM.signed (hookDeltaWord out parse)))}
def afterLiquidityBranchResult (f : Frame) (post : State) (delta : UInt256)
    (z : Bool) (payload out : ByteArray) (parse : Bool) : ExecResult :=
  if z = true ∧ hookReplyValid payload out then
    if parse = true ∧ out.size ≠ 64 then .reverted
    else afterLiquidityFinishResult (afterLiquidityReplyFrame f payload out parse) post delta (hookDeltaWord out parse)
  else .reverted

theorem afterLiquidityBranchBody {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : ModifyLiquidityWords} {delta fees : UInt256} {data out : ByteArray}
    {z : Bool} {old : Value} (add : Bool)
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (modifyLiquidityParamsValue p))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta)))
    (he : f.locals.get? "feesAccrued" = some (.int (EVM.signed fees)))
    (hb : f.locals.get? "hookData" = some (.bytes data))
    (hcaller : f.locals.get? "callerDelta" = some (.int (EVM.signed delta)))
    (hhook : f.locals.get? "hookDelta" = some old)
    (hc : PoolKeyCanonical key) (hl : int24Canonical p.lower) (hu : int24Canonical p.upper)
    (hcall : callViaEVM evm hook 0 (afterLiquidityPayload add evm.executionEnv.source key p delta fees data) (z, post, out)) :
    ExecBlock config f evm (afterLiquidityBranch add)
      (afterLiquidityBranchResult f post delta z (afterLiquidityPayload add evm.executionEnv.source key p delta fees data)
        out (afterLiquidityParse hook add)) := by
  let payload := afterLiquidityPayload add evm.executionEnv.source key p delta fees data
  let f1 := {f with locals := f.locals.insert "payload" (.bytes payload)}
  have hs1 : f1.locals.get? "self" = some (.address hook) :=
    (store_get_ne _ _ (by decide : ("payload" == "self") = false)).trans hs
  have hpayload := liquidityHookPayload_eval true add
    (show evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) by simp only [evalExpr?, envValue, pure])
    (evalLocalValue hk) (evalLocalValue hp) (evalLocalValue hd) (evalLocalValue he) (evalLocalValue hb) hc hl hu
  have hparse := hookPermission_eval (evalLocalValue (cfg := config) (evm := evm) hs1)
    (afterLiquidityDeltaFlag add) (by cases add <;> decide)
  have hinvoke := hookDeltaCall (f := f1) (parse := afterLiquidityParse hook add)
    hf (evalLocalValue hs1) (evalLocalValue (store_get_self _ _ _)) hparse
    (by change 4 ≤ (liquidityHookPayload true add _ _ _ _ _ _).size; rw [liquidityHookPayload_size]; change 4 ≤ 452+_; omega)
    hcall "result"
  by_cases hv : z = true ∧ hookReplyValid payload out
  · rw [hookDeltaInvocationResult, if_pos hv] at hinvoke
    rw [afterLiquidityBranchResult, if_pos hv]
    by_cases hbad : afterLiquidityParse hook add = true ∧ out.size ≠ 64
    · rw [if_pos hbad] at hinvoke ⊢
      exact ExecBlock.consNormal (ExecStmt.letDecl hpayload) (ExecBlock.consRevert hinvoke)
    · rw [if_neg hbad] at hinvoke ⊢
      have hfinish := afterLiquidityFinish (f := afterLiquidityReplyFrame f payload out (afterLiquidityParse hook add))
        (evm := post) hf
        ((store_get_ne _ _ (by decide : ("result" == "callerDelta") = false)).trans
          ((store_get_ne _ _ (by decide : ("payload" == "callerDelta") = false)).trans hcaller))
        ((store_get_ne _ _ (by decide : ("result" == "hookDelta") = false)).trans
          ((store_get_ne _ _ (by decide : ("payload" == "hookDelta") = false)).trans hhook))
        (store_get_self _ _ _)
      exact ExecBlock.consNormal (ExecStmt.letDecl hpayload) (ExecBlock.consNormal hinvoke hfinish)
  · rw [hookDeltaInvocationResult, if_neg hv] at hinvoke
    rw [afterLiquidityBranchResult, if_neg hv]
    exact ExecBlock.consNormal (ExecStmt.letDecl hpayload) (ExecBlock.consRevert hinvoke)

end Benchmarks.UniswapV4PoolManager
