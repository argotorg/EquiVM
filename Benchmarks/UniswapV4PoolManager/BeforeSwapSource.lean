import Benchmarks.UniswapV4PoolManager.BeforeSwapBranchSource
import Benchmarks.UniswapV4PoolManager.BlockContinuation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev beforeSwapFunction : FunctionDecl := contract.functions[37]!
def beforeSwapActive (hook : AccountAddress) : Prop := UInt256.land (accountWord hook) ⟨128⟩ ≠ ⟨0⟩
instance (hook : AccountAddress) : Decidable (beforeSwapActive hook) := inferInstanceAs (Decidable (_ ≠ _))
def beforeSwapPreludeFrame (f : Frame) (p : SwapParamsWords) : Frame :=
  valueLocal (valueLocal (valueLocal f "amountToSwap" (.int (EVM.signed p.amountSpecified)))
    "hookReturn" (.int 0)) "lpFeeOverride" (.int 0)
def beforeSwapSelectedResult (f : Frame) (evm post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  if beforeSwapActive hook then beforeSwapBranchResult f post hook key p.amountSpecified z
    (beforeSwapPayload evm.executionEnv.source key p data) out
  else .ok f evm
def beforeSwapReturnValues (amount hookReturn fee : UInt256) : List Value :=
  [.int (EVM.signed amount), .int (EVM.signed hookReturn), .int (Int.ofNat fee.toNat)]
def beforeSwapReturnResult (f : Frame) (evm : State) (hook : AccountAddress) (key : PoolKeyWords)
    (amount : UInt256) (out : ByteArray) : ExecResult :=
  .returned f evm (some (if beforeSwapActive hook then
    beforeSwapReturnValues (beforeSwapReplyAmount hook amount out) (beforeSwapReplyHook hook out) (beforeSwapFee key out)
    else beforeSwapReturnValues amount ⟨0⟩ ⟨0⟩))
def beforeSwapBlockResult (f : Frame) (evm post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  if evm.executionEnv.source = hook then
    .returned (beforeSwapPreludeFrame f p) evm (some (beforeSwapReturnValues p.amountSpecified ⟨0⟩ ⟨0⟩))
  else continueBlockResult (fun f' next => beforeSwapReturnResult f' next hook key p.amountSpecified out)
    (beforeSwapSelectedResult (beforeSwapPreludeFrame f p) evm post hook key p data z out)
def beforeSwapResult (f : Frame) (evm post : State) (hook : AccountAddress) (key : PoolKeyWords)
    (p : SwapParamsWords) (data : ByteArray) (z : Bool) (out : ByteArray) : ExecResult :=
  finishBlockResult (beforeSwapBlockResult f evm post hook key p data z out)

theorem beforeSwapSelectedSource {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {data out : ByteArray} {z : Bool} {oldHook oldFee : Value}
    (hc : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "hookData" = some (.bytes data))
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed p.amountSpecified)))
    (hh : f.locals.get? "hookReturn" = some oldHook)
    (hf : f.locals.get? "lpFeeOverride" = some oldFee)
    (hkey : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hcall : beforeSwapActive hook →
      callViaEVM evm hook 0 (beforeSwapPayload evm.executionEnv.source key p data) (z, post, out)) :
    ExecStmt config f evm beforeSwapFunction.body[4]!
      (beforeSwapSelectedResult f evm post hook key p data z out) := by
  have hflag := hookPermission_eval (evalLocalValue (cfg := config) (evm := evm) hs) ⟨128⟩ (by decide)
  change evalExpr? config f evm _ = .ok (.bool (decide (beforeSwapActive hook))) at hflag
  by_cases he : beforeSwapActive hook
  · rw [beforeSwapSelectedResult, if_pos he]
    exact ExecStmt.iteTrue (hflag.trans (by rw [decide_eq_true he]))
      (beforeSwapBranchSource hc hs hk hp hd ha hh hf hkey hlimit (hcall he))
  · rw [beforeSwapSelectedResult, if_neg he]
    exact ExecStmt.iteFalse (hflag.trans (by rw [decide_eq_false he])) ExecBlock.nil

theorem beforeSwapReturnSource {f : Frame} {evm : State} {amount hookReturn fee : UInt256}
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed amount)))
    (hh : f.locals.get? "hookReturn" = some (.int (EVM.signed hookReturn)))
    (hf : f.locals.get? "lpFeeOverride" = some (.int (Int.ofNat fee.toNat))) :
    ExecBlock config f evm [.return [.var "amountToSwap", .var "hookReturn", .var "lpFeeOverride"]]
      (.returned f evm (some (beforeSwapReturnValues amount hookReturn fee))) := by
  exact ExecBlock.consReturn (ExecStmt.return (by
    simp only [evalExprs?, evalLocalValue ha, evalLocalValue hh, evalLocalValue hf,
      bind, EvalResult.bind, pure]; rfl))

theorem beforeSwapSelectedReturn {f f' : Frame} {evm post next : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {data out : ByteArray} {z : Bool}
    (ha : f.locals.get? "amountToSwap" = some (.int (EVM.signed p.amountSpecified)))
    (hh : f.locals.get? "hookReturn" = some (.int 0))
    (hf : f.locals.get? "lpFeeOverride" = some (.int 0))
    (hr : beforeSwapSelectedResult f evm post hook key p data z out = .ok f' next) :
    ExecBlock config f' next [.return [.var "amountToSwap", .var "hookReturn", .var "lpFeeOverride"]]
      (beforeSwapReturnResult f' next hook key p.amountSpecified out) := by
  by_cases he : beforeSwapActive hook
  · rw [beforeSwapSelectedResult, if_pos he] at hr
    obtain ⟨_, ha', hh', hf'⟩ := beforeSwapBranchResult_locals ha hh hf hr
    rw [beforeSwapReturnResult, if_pos he]
    exact beforeSwapReturnSource ha' hh' hf'
  · rw [beforeSwapSelectedResult, if_neg he] at hr
    cases hr
    rw [beforeSwapReturnResult, if_neg he]
    exact beforeSwapReturnSource (hookReturn := ⟨0⟩) (fee := ⟨0⟩) ha hh hf

theorem beforeSwapPrelude_get (f : Frame) (p : SwapParamsWords) (name : Ident)
    (ha : ("amountToSwap" == name) = false) (hh : ("hookReturn" == name) = false)
    (hf : ("lpFeeOverride" == name) = false) :
    (beforeSwapPreludeFrame f p).locals.get? name = f.locals.get? name :=
  store_get_ne3 _ _ _ _ ha hh hf

theorem beforeSwapBody {f : Frame} {evm post : State} {hook : AccountAddress}
    {key : PoolKeyWords} {p : SwapParamsWords} {data out : ByteArray} {z : Bool}
    (hc : f.contract = contract) (hs : f.locals.get? "self" = some (.address hook))
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "params" = some (swapParamsValue p))
    (hd : f.locals.get? "hookData" = some (.bytes data))
    (hkey : PoolKeyCanonical key) (hlimit : p.priceLimit.toNat < 2^160)
    (hcall : evm.executionEnv.source ≠ hook → beforeSwapActive hook →
      callViaEVM evm hook 0 (beforeSwapPayload evm.executionEnv.source key p data) (z, post, out)) :
    ExecFuncBody config f evm beforeSwapFunction.body (beforeSwapResult f evm post hook key p data z out) := by
  let f0 := beforeSwapPreludeFrame f p
  have hget := beforeSwapPrelude_get f p
  have hself : f0.locals.get? "self" = some (.address hook) :=
    (hget "self" (by decide) (by decide) (by decide)).trans hs
  have hamount : f0.locals.get? "amountToSwap" = some (.int (EVM.signed p.amountSpecified)) :=
    (store_get_ne2 _ _ _ (by decide : ("hookReturn" == "amountToSwap") = false)
      (by decide : ("lpFeeOverride" == "amountToSwap") = false)).trans (store_get_self _ _ _)
  have hhook : f0.locals.get? "hookReturn" = some (.int 0) :=
    (store_get_ne _ _ (by decide : ("lpFeeOverride" == "hookReturn") = false)).trans (store_get_self _ _ _)
  have hfee : f0.locals.get? "lpFeeOverride" = some (.int 0) := store_get_self _ _ _
  have hpre : ExecBlock config f evm (beforeSwapFunction.body.take 3) (.ok f0 evm) := by
    have hfield := evalStructField (evalLocalValue (cfg := config) (evm := evm) hp) (field := "amountSpecified") rfl
    exact ExecBlock.consNormal (ExecStmt.letDecl hfield)
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
        (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil))
  have heq := evalEqAddress
    (show evalExpr? config f0 evm (.env .caller) = .ok (.address evm.executionEnv.source) by
      simp only [evalExpr?, envValue, pure]) (evalLocalValue hself)
  apply execFuncBody_block
  by_cases hcaller : evm.executionEnv.source = hook
  · rw [beforeSwapBlockResult, if_pos hcaller]
    apply execBlock_append hpre
    exact ExecBlock.consReturn (ExecStmt.iteTrue (heq.trans (by rw [decide_eq_true hcaller]))
      (ExecBlock.consReturn (ExecStmt.return (by
        simp only [evalExprs?, evalLocalValue hamount, evalExpr?, bind, EvalResult.bind, pure]; rfl))))
  · rw [beforeSwapBlockResult, if_neg hcaller]
    have hsel := beforeSwapSelectedSource (f := f0) hc hself
      ((hget "key" (by decide) (by decide) (by decide)).trans hk)
      ((hget "params" (by decide) (by decide) (by decide)).trans hp)
      ((hget "hookData" (by decide) (by decide) (by decide)).trans hd)
      hamount hhook hfee hkey hlimit (hcall hcaller)
    have htail : ExecBlock config f0 evm (beforeSwapFunction.body.drop 4)
        (continueBlockResult (fun f' next => beforeSwapReturnResult f' next hook key p.amountSpecified out)
          (beforeSwapSelectedResult f0 evm post hook key p data z out)) := by
      apply execBlock_continue (execBlock_singleton hsel)
      intro f' next hr
      exact beforeSwapSelectedReturn hamount hhook hfee hr
    exact execBlock_append hpre (ExecBlock.consNormal
      (ExecStmt.iteFalse (heq.trans (by rw [decide_eq_false hcaller])) ExecBlock.nil) htail)

end Benchmarks.UniswapV4PoolManager
