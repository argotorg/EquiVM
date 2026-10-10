import Benchmarks.UniswapV4PoolManager.AfterSwapUpdateSource
import Benchmarks.UniswapV4PoolManager.SwapHookSource
import Benchmarks.UniswapV4PoolManager.HookDeltaSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev afterSwapFunction : FunctionDecl := contract.functions[38]!
def afterSwapActive (hook : AccountAddress) : Prop := UInt256.land (accountWord hook) ⟨64⟩ ≠ ⟨0⟩
instance (hook : AccountAddress) : Decidable (afterSwapActive hook) := inferInstanceAs (Decidable (_ ≠ _))
def afterSwapParse (hook : AccountAddress) : Bool := decide (UInt256.land (accountWord hook) ⟨4⟩ ≠ ⟨0⟩)
def afterSwapPayload (sender : AccountAddress) (key : PoolKeyWords) (p : SwapParamsWords)
    (delta : UInt256) (data : ByteArray) : ByteArray := swapHookPayload true sender key p delta data
def afterSwapPayloadExpr : Expr :=
  swapHookPayloadExpr true (.env .caller) (.var "key") (.var "params") (.var "swapDelta") (.var "hookData")
def afterSwapBranchStmts : List Stmt :=
  [.letDecl "payload" (some .bytes) afterSwapPayloadExpr,
   .internalCall "Hooks_callHookWithReturnDelta" [.var "self", .var "payload",
     hookPermissionExpr (.var "self") ⟨4⟩] "result"] ++ afterSwapUpdateStmts
def afterSwapReplyFrame (f : Frame) (payload out : ByteArray) (parse : Bool) : Frame :=
  valueLocal (valueLocal f "payload" (.bytes payload)) "result" (.int (EVM.signed (hookDeltaWord out parse)))
def afterSwapBranchResult (f : Frame) (post : State) (unspecified : Int)
    (z : Bool) (payload out : ByteArray) (parse : Bool) : ExecResult :=
  if z = true ∧ hookReplyValid payload out then
    if parse = true ∧ out.size ≠ 64 then .reverted
    else afterSwapUpdateResult (afterSwapReplyFrame f payload out parse) post unspecified (hookDeltaWord out parse)
  else .reverted

theorem afterSwapBranchSource {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {delta : UInt256} {unspecified : Int}
    {data out : ByteArray} {z : Bool}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "swapDelta" = some (.int (EVM.signed delta)))
    (hb : f.locals.get? "hookData" = some (.bytes data))
    (hu : f.locals.get? "unspecified" = some (.int unspecified))
    (hc : PoolKeyCanonical key) (hl : p.priceLimit.toNat < 2^160)
    (hcall : callViaEVM evm hook 0 (afterSwapPayload evm.executionEnv.source key p delta data) (z, post, out)) :
    ExecBlock config f evm afterSwapBranchStmts
      (afterSwapBranchResult f post unspecified z (afterSwapPayload evm.executionEnv.source key p delta data)
        out (afterSwapParse hook)) := by
  let payload := afterSwapPayload evm.executionEnv.source key p delta data
  let f1 := valueLocal f "payload" (.bytes payload)
  have hs1 : f1.locals.get? "self" = some (.address hook) :=
    (store_get_ne _ _ (by decide : ("payload" == "self") = false)).trans hs
  have hencode := swapHookPayload_eval true
    (show evalExpr? config f evm (.env .caller) = .ok (.address evm.executionEnv.source) by
      simp only [evalExpr?, envValue, pure])
    (evalLocalValue hk) (evalLocalValue hp) (evalLocalValue hd) (evalLocalValue hb) hc hl
  have hparse := hookPermission_eval (evalLocalValue (cfg := config) (evm := evm) hs1) ⟨4⟩ (by decide)
  have hinvoke := hookDeltaCall (f := f1) (parse := afterSwapParse hook) hf
    (evalLocalValue hs1) (evalLocalValue (store_get_self _ _ _)) hparse
    (by change 4 ≤ (swapHookPayload true _ _ _ _ _).size; rw [swapHookPayload_size]; change 4 ≤ 388+_; omega)
    hcall "result"
  by_cases hv : z = true ∧ hookReplyValid payload out
  · rw [hookDeltaInvocationResult, if_pos hv] at hinvoke
    rw [afterSwapBranchResult, if_pos hv]
    by_cases hbad : afterSwapParse hook = true ∧ out.size ≠ 64
    · rw [if_pos hbad] at hinvoke ⊢
      exact ExecBlock.consNormal (ExecStmt.letDecl hencode) (ExecBlock.consRevert hinvoke)
    · rw [if_neg hbad] at hinvoke ⊢
      have hu' : (afterSwapReplyFrame f payload out (afterSwapParse hook)).locals.get? "unspecified" =
          some (.int unspecified) :=
        (store_get_ne2 _ _ _ (by decide : ("payload" == "unspecified") = false)
          (by decide : ("result" == "unspecified") = false)).trans hu
      exact ExecBlock.consNormal (ExecStmt.letDecl hencode) (ExecBlock.consNormal hinvoke
        (afterSwapUpdateSource (f := afterSwapReplyFrame f payload out (afterSwapParse hook)) hf hu' (store_get_self _ _ _)))
  · rw [hookDeltaInvocationResult, if_neg hv] at hinvoke
    rw [afterSwapBranchResult, if_neg hv]
    exact ExecBlock.consNormal (ExecStmt.letDecl hencode) (ExecBlock.consRevert hinvoke)

theorem afterSwapBranchResult_normal {f f' : Frame} {evm post : State} {unspecified : Int}
    {z parse : Bool} {payload out : ByteArray}
    (hr : afterSwapBranchResult f evm unspecified z payload out parse = .ok f' post) :
    f' = afterSwapUpdateFrame (afterSwapReplyFrame f payload out parse) unspecified (hookDeltaWord out parse) ∧
      post = evm ∧ signedFits ⟨128, by decide⟩ (unspecified+EVM.signed (hookDeltaWord out parse)) := by
  rw [afterSwapBranchResult] at hr
  split_ifs at hr with hv hbad
  exact afterSwapUpdateResult_normal hr

end Benchmarks.UniswapV4PoolManager
