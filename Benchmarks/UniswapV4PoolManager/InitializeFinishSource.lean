import Benchmarks.UniswapV4PoolManager.InitializeHookCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def initializeFinishResult (f : Frame) (evm evm' : EVM.State) (key : PoolKeyWords)
    (price tick : UInt256) (z : Bool) (out : ByteArray) : ExecResult :=
  let finalFrame := {f with locals := f.locals.insert "__c6" .unit}
  if hookEnabled evm.executionEnv.source (AccountAddress.ofNat key.hooks.toNat) ⟨4096⟩ then
    if z = true ∧ hookReplyValid (afterInitializePayload evm.executionEnv.source key price tick) out then
      .returned finalFrame evm' (some [.int (EVM.signed tick)])
    else .reverted
  else .returned finalFrame evm (some [.int (EVM.signed tick)])

theorem initializeFinishSource {f : Frame} {evm evm' : EVM.State} {key : PoolKeyWords}
    {price tick : UInt256} {z : Bool} {out : ByteArray}
    (hf : f.contract = contract) (hc : PoolKeyCanonical key)
    (hprice : price.toNat < 2^160) (htick : int24Canonical tick)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? "tick" = some (.int (EVM.signed tick)))
    (hcall : hookEnabled evm.executionEnv.source (AccountAddress.ofNat key.hooks.toNat) ⟨4096⟩ →
      callViaEVM evm (AccountAddress.ofNat key.hooks.toNat) 0
        (afterInitializePayload evm.executionEnv.source key price tick) (z, evm', out)) :
    ExecFuncBody config f evm (initializeTransition.body.drop 18)
      (initializeFinishResult f evm evm' key price tick z out) := by
  have hkey := evalLocalValue (cfg := config) (evm := evm) hk
  have hs := afterInitializeCall hf (evalStructField hkey (field := "hooks") rfl)
    hkey (evalLocalValue hp) (evalLocalValue ht) hc hprice htick hcall "__c6"
  have hreturn (state : EVM.State) : ExecFuncBody config
      {f with locals := f.locals.insert "__c6" .unit} state (initializeTransition.body.drop 19)
      (.returned {f with locals := f.locals.insert "__c6" .unit} state (some [.int (EVM.signed tick)])) :=
    .execBlockRet (ABlock.start.returns (evalLocalValue
      ((store_get_ne _ _ (by decide : ("__c6" == "tick") = false)).trans ht)))
  simp only [hookInvocationResult, resumeCallResult_ite, resumeCallResult_returned,
    resumeCallResult_reverted] at hs
  unfold initializeFinishResult
  split_ifs at hs ⊢
  · exact execFuncBody_prepend (execBlock_singleton hs) (hreturn evm')
  · exact .execBlockRevert (ExecBlock.consRevert hs)
  · exact execFuncBody_prepend (execBlock_singleton hs) (hreturn evm)

theorem initializeEmitSource {f : Frame} {evm : EVM.State} {key : PoolKeyWords} {price tick id : UInt256}
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? "tick" = some (.int (EVM.signed tick)))
    (hi : f.locals.get? "id" = some (wordBytes32Value id)) :
    ExecStmt config f evm initializeTransition.body[17]! (.ok f evm) := by
  have hkey := evalLocalValue (cfg := config) (evm := evm) hk
  apply ExecStmt.emit (vals := [wordBytes32Value id,
    .address (AccountAddress.ofNat key.currency0.toNat), .address (AccountAddress.ofNat key.currency1.toNat),
    .int (Int.ofNat key.fee.toNat), .int (EVM.signed key.tickSpacing),
    .address (AccountAddress.ofNat key.hooks.toNat), .int (Int.ofNat price.toNat), .int (EVM.signed tick)])
  have h0 := evalStructField hkey (field := "currency0") rfl
  have h1 := evalStructField hkey (field := "currency1") rfl
  have h2 := evalStructField hkey (field := "fee") rfl
  have h3 := evalStructField hkey (field := "tickSpacing") rfl
  have h4 := evalStructField hkey (field := "hooks") rfl
  change evalExprs? config f evm [.var "id", .field (.var "key") "currency0",
    .field (.var "key") "currency1", .field (.var "key") "fee", .field (.var "key") "tickSpacing",
    .field (.var "key") "hooks", .var "sqrtPriceX96", .var "tick"] = _
  simp only [evalExprs?, h0, h1, h2, h3, h4, evalLocalValue hi, evalLocalValue hp,
    evalLocalValue ht, bind, EvalResult.bind, pure]

theorem initializeAfterPoolSource {f : Frame} {evm evm' : EVM.State} {key : PoolKeyWords}
    {price tick id : UInt256} {z : Bool} {out : ByteArray} {old : Value}
    (hf : f.contract = contract) (hc : PoolKeyCanonical key)
    (hprice : price.toNat < 2^160) (htick : int24Canonical tick)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (ht : f.locals.get? "__c5" = some (.int (EVM.signed tick)))
    (hi : f.locals.get? "id" = some (wordBytes32Value id)) (hold : f.locals.get? "tick" = some old)
    (hcall : hookEnabled evm.executionEnv.source (AccountAddress.ofNat key.hooks.toNat) ⟨4096⟩ →
      callViaEVM evm (AccountAddress.ofNat key.hooks.toNat) 0
        (afterInitializePayload evm.executionEnv.source key price tick) (z, evm', out)) :
    ExecFuncBody config f evm (initializeTransition.body.drop 16)
      (initializeFinishResult {f with locals := f.locals.insert "tick" (.int (EVM.signed tick))}
        evm evm' key price tick z out) := by
  let f1 : Frame := {f with locals := f.locals.insert "tick" (.int (EVM.signed tick))}
  have hk1 : f1.locals.get? "key" = some (poolKeyValue key) :=
    (store_get_ne _ _ (by decide : ("tick" == "key") = false)).trans hk
  have hp1 : f1.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) :=
    (store_get_ne _ _ (by decide : ("tick" == "sqrtPriceX96") = false)).trans hp
  have hi1 : f1.locals.get? "id" = some (wordBytes32Value id) :=
    (store_get_ne _ _ (by decide : ("tick" == "id") = false)).trans hi
  have ht1 : f1.locals.get? "tick" = some (.int (EVM.signed tick)) := store_get_self _ _ _
  have hs : ExecBlock config f evm ((initializeTransition.body.drop 16).take 2) (.ok f1 evm) :=
    ExecBlock.consNormal (ExecStmt.assign (evalLocalValue ht) (assignLocalValue hold))
      (ExecBlock.consNormal (initializeEmitSource hk1 hp1 ht1 hi1) ExecBlock.nil)
  exact execFuncBody_prepend hs (initializeFinishSource hf hc hprice htick hk1 hp1 ht1 hcall)

end Benchmarks.UniswapV4PoolManager
