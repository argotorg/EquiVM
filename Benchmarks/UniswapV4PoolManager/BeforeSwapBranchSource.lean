import Benchmarks.UniswapV4PoolManager.BeforeSwapReplySource
import Benchmarks.UniswapV4PoolManager.SwapHookSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def beforeSwapPayload (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords) (data : ByteArray) : ByteArray :=
  swapHookPayload false sender key p ⟨0⟩ data
def beforeSwapPayloadExpr : Expr :=
  swapHookPayloadExpr false (.env .caller) (.var "key") (.var "params") (.intLit 0) (.var "hookData")
def beforeSwapHookFrame (f : Frame) (payload out : ByteArray) : Frame :=
  valueLocal (valueLocal f "payload" (.bytes payload)) "result" (.bytes out)
def beforeSwapBranchStmts : List Stmt :=
  [.letDecl "payload" (some .bytes) beforeSwapPayloadExpr,
   .internalCall "Hooks_callHook" [.var "self", .var "payload"] "result"] ++ beforeSwapReplyStmts
def beforeSwapBranchResult (f : Frame) (post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (amount : UInt256) (z : Bool) (payload out : ByteArray) : ExecResult :=
  if z = true ∧ hookReplyValid payload out then
    beforeSwapReplyResult (beforeSwapHookFrame f payload out) post hook key amount out
  else .reverted

theorem beforeSwapHookFrame_get (f : Frame) (payload out : ByteArray) (name : Ident)
    (hp : ("payload" == name) = false) (hr : ("result" == name) = false) :
    (beforeSwapHookFrame f payload out).locals.get? name = f.locals.get? name :=
  store_get_ne2 _ _ _ hp hr

theorem beforeSwapBranchSource {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {data out : ByteArray} {z : Bool} {oldHook oldFee : Value}
    (hc : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "hookData" = some (.bytes data))
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed p.amountSpecified)))
    (hh : f.locals.get? "hookReturn" = some oldHook)
    (hf : f.locals.get? "lpFeeOverride" = some oldFee)
    (hkey : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hcall : callViaEVM evm hook 0 (beforeSwapPayload evm.executionEnv.source key p data) (z, post, out)) :
    ExecBlock config f evm beforeSwapBranchStmts
      (beforeSwapBranchResult f post hook key p.amountSpecified z
        (beforeSwapPayload evm.executionEnv.source key p data) out) := by
  let payload := beforeSwapPayload evm.executionEnv.source key p data
  let f1 := valueLocal f "payload" (.bytes payload)
  have hencode := swapHookPayload_eval (delta := ⟨0⟩) false
    (show evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) by
      simp only [evalExpr?, envValue, pure])
    (evalLocalValue hk) (evalLocalValue hp)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (EVM.signed (⟨0⟩ : UInt256))) by
      simp only [evalExpr?, pure]; rfl)
    (evalLocalValue hd) hkey hlimit
  have hinvoke := hookCall (f := f1) hc
    (evalLocalValue ((store_get_ne _ _ (by decide : ("payload" == "self") = false)).trans hs))
    (evalLocalValue (store_get_self _ _ _))
    (by change 4 ≤ (swapHookPayload false _ _ _ _ _).size; rw [swapHookPayload_size]; change 4 ≤ 356+_; omega)
    hcall "result"
  by_cases hv : z = true ∧ hookReplyValid payload out
  · rw [if_pos hv] at hinvoke
    rw [beforeSwapBranchResult, if_pos hv]
    have hget := beforeSwapHookFrame_get f payload out
    have hreply := beforeSwapReplySource (evm := post)
      ((hget "self" (by decide) (by decide)).trans hs)
      ((hget "key" (by decide) (by decide)).trans hk)
      ((hget "amountToSwap" (by decide) (by decide)).trans ha)
      ((hget "hookReturn" (by decide) (by decide)).trans hh)
      ((hget "lpFeeOverride" (by decide) (by decide)).trans hf) (store_get_self _ _ _)
    exact ExecBlock.consNormal (ExecStmt.letDecl hencode) (ExecBlock.consNormal hinvoke hreply)
  · rw [if_neg hv] at hinvoke
    rw [beforeSwapBranchResult, if_neg hv]
    exact ExecBlock.consNormal (ExecStmt.letDecl hencode) (ExecBlock.consRevert hinvoke)

theorem beforeSwapBranchResult_locals {f f' : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {amount : UInt256} {z : Bool} {payload out : ByteArray}
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hh : f.locals.get? "hookReturn" = some (.int 0))
    (hf : f.locals.get? "lpFeeOverride" = some (.int 0))
    (hr : beforeSwapBranchResult f evm hook key amount z payload out = .ok f' post) :
    post = evm ∧
    f'.locals.get? "amountToSwap" = some (.int (EVM.signed (beforeSwapReplyAmount hook amount out))) ∧
    f'.locals.get? "hookReturn" = some (.int (EVM.signed (beforeSwapReplyHook hook out))) ∧
    f'.locals.get? "lpFeeOverride" = some (.int (Int.ofNat (beforeSwapFee key out).toNat)) := by
  rw [beforeSwapBranchResult] at hr
  split_ifs at hr with hv
  have hget := beforeSwapHookFrame_get f payload out
  exact beforeSwapReplyResult_locals ((hget "amountToSwap" (by decide) (by decide)).trans ha)
    ((hget "hookReturn" (by decide) (by decide)).trans hh)
    ((hget "lpFeeOverride" (by decide) (by decide)).trans hf) hr

end Benchmarks.UniswapV4PoolManager
