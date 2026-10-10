import Benchmarks.UniswapV4PoolManager.PoolInitializeSource
import Benchmarks.UniswapV4PoolManager.InitializeFinishSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def initializePoolAlias : Ident := "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.21"
def initializePoolFrame (f : Frame) (key : PoolKeyWords) : Frame :=
  {f with locals := ((f.locals.insert "id" (wordBytes32Value (poolKeyId key))).insert
    initializePoolAlias (poolRefValue (poolKeyId key)))}

@[irreducible] def initializePoolResult (f : Frame) (evm evm' : EVM.State)
    (key : PoolKeyWords) (price fee : UInt256) (z : Bool) (out : ByteArray) : ExecResult :=
  if poolSqrtPriceWord evm (poolKeyId key) ≠ ⟨0⟩ then .reverted else
    match tickPriceResult price with
    | none => .reverted
    | some tick =>
      if evm.executionEnv.perm = false then .staticViolation else
      initializeFinishResult
        {(initializePoolFrame f key) with locals := ((initializePoolFrame f key).locals.insert
          "__c5" (.int (EVM.signed tick))).insert "tick" (.int (EVM.signed tick))}
        (poolInitializePost evm (poolKeyId key) price tick fee) evm' key price tick z out

theorem initializePoolSource {f : Frame} {evm evm' : EVM.State} {key : PoolKeyWords}
    {price fee : UInt256} {z : Bool} {out : ByteArray} {old : Value}
    (hf : f.contract = contract) (hc : PoolKeyCanonical key)
    (hprice : price.toNat < 2^160) (hfee : fee.toNat < 2^24)
    (hk : f.locals.get? "key" = some (poolKeyValue key))
    (hp : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)))
    (he : f.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat)))
    (ht : f.locals.get? "tick" = some old) (hb : f.locals.get? "_pools" = none)
    (hcall : ∀ tick, poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩ →
      tickPriceResult price = some tick → evm.executionEnv.perm = true →
      hookEnabled evm.executionEnv.source (AccountAddress.ofNat key.hooks.toNat) ⟨4096⟩ →
      callViaEVM (poolInitializePost evm (poolKeyId key) price tick fee)
        (AccountAddress.ofNat key.hooks.toNat) 0
        (afterInitializePayload evm.executionEnv.source key price tick) (z, evm', out)) :
    ExecFuncBody config f evm (initializeTransition.body.drop 13)
      (initializePoolResult f evm evm' key price fee z out) := by
  let f1 : Frame := {f with locals := f.locals.insert "id" (wordBytes32Value (poolKeyId key))}
  let f2 := initializePoolFrame f key
  have hid := poolIdCall hf hc (evalLocalValue (cfg := config) (evm := evm) hk) "id"
  have href : ExecStmt config f1 evm initializeTransition.body[14]! (.ok f2 evm) :=
    ExecStmt.letStorage (poolMappingResolve (f := f1) hf
      ((store_get_ne _ _ (by decide : ("id" == "_pools") = false)).trans hb)
      (evalLocalValue (store_get_self _ _ _)))
  have hp2 : f2.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("id" == "sqrtPriceX96") = false)
      (by decide : (initializePoolAlias == "sqrtPriceX96") = false)).trans hp
  have he2 : f2.locals.get? "lpFee" = some (.int (Int.ofNat fee.toNat)) :=
    (store_get_ne2 _ _ _ (by decide : ("id" == "lpFee") = false)
      (by decide : (initializePoolAlias == "lpFee") = false)).trans he
  have hpre : ExecBlock config f evm ((initializeTransition.body.drop 13).take 2) (.ok f2 evm) :=
    ExecBlock.consNormal hid (ExecBlock.consNormal href ExecBlock.nil)
  have hpool := poolInitializeCall (f := f2) (evm := evm) hf hprice hfee
    (evalLocalValue (store_get_self _ _ _)) (evalLocalValue hp2) (evalLocalValue he2) "__c5"
  unfold initializePoolResult
  simp only [poolInitializeCallResult, poolInitializeResult] at hpool
  by_cases hz : poolSqrtPriceWord evm (poolKeyId key) ≠ ⟨0⟩
  · simp only [if_pos hz, resumeCallResult_reverted] at hpool ⊢
    exact execFuncBody_prepend hpre (.execBlockRevert (ExecBlock.consRevert hpool))
  · simp only [if_neg hz] at hpool ⊢
    cases hresult : tickPriceResult price with
    | none =>
      simp only [hresult, resumeCallResult_reverted] at hpool ⊢
      exact execFuncBody_prepend hpre (.execBlockRevert (ExecBlock.consRevert hpool))
    | some tick =>
      simp only [hresult, poolInitializeTailResult, resumeCallResult_ite, resumeCallResult_static,
        resumeCallResult_returned] at hpool ⊢
      by_cases hperm : evm.executionEnv.perm = false
      · simp only [if_pos hperm] at hpool ⊢
        exact execFuncBody_prepend hpre (.execBlockStatic (ExecBlock.consStatic hpool))
      · simp only [if_neg hperm] at hpool ⊢
        let f3 : Frame := {f2 with locals := f2.locals.insert "__c5" (.int (EVM.signed tick))}
        have hk3 : f3.locals.get? "key" = some (poolKeyValue key) :=
          (store_get_ne3 _ _ _ _ (by decide : ("id" == "key") = false)
            (by decide : (initializePoolAlias == "key") = false)
            (by decide : ("__c5" == "key") = false)).trans hk
        have hp3 : f3.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) :=
          (store_get_ne _ _ (by decide : ("__c5" == "sqrtPriceX96") = false)).trans hp2
        have hi3 : f3.locals.get? "id" = some (wordBytes32Value (poolKeyId key)) :=
          (store_get_ne2 _ _ _ (by decide : (initializePoolAlias == "id") = false)
            (by decide : ("__c5" == "id") = false)).trans (store_get_self _ _ _)
        have ht3 : f3.locals.get? "tick" = some old :=
          (store_get_ne3 _ _ _ _ (by decide : ("id" == "tick") = false)
            (by decide : (initializePoolAlias == "tick") = false)
            (by decide : ("__c5" == "tick") = false)).trans ht
        have hafter := initializeAfterPoolSource (f := f3)
          (evm := poolInitializePost evm (poolKeyId key) price tick fee) hf hc hprice
          (tickPriceResult_canonical hresult) hk3 hp3 (store_get_self _ _ _) hi3 ht3
          (by simpa only [poolInitializePost, storageStore_executionEnv] using
            hcall tick (not_not.mp hz) hresult (Bool.eq_true_of_not_eq_false hperm))
        exact execFuncBody_prepend hpre (execFuncBody_prepend (execBlock_singleton hpool) hafter)

end Benchmarks.UniswapV4PoolManager
