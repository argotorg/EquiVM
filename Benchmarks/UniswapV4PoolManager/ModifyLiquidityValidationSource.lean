import Benchmarks.UniswapV4PoolManager.ModifyLiquidityPreludeSource
import Benchmarks.UniswapV4PoolManager.TransientSource
import Benchmarks.UniswapV4PoolManager.NoDelegateCall
import Benchmarks.UniswapV4PoolManager.PoolProtocolFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.UniswapV4PoolManager.Immutables
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def modifyLiquidityCheckAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.24"

def modifyLiquidityValidationFrame (f : Frame) (key : PoolKeyWords) : Frame :=
  let locals := f.locals.insert "__c0" (.bool true)
  let locals := locals.insert "__c1" .unit
  let locals := locals.insert "id" (wordBytes32Value (poolKeyId key))
  let locals := locals.insert "__c3" (poolRefValue (poolKeyId key))
  let locals := locals.insert "pool" (poolRefValue (poolKeyId key))
  let locals := locals.insert modifyLiquidityCheckAlias (poolRefValue (poolKeyId key))
  {f with locals := locals.insert "__c4" .unit}

def modifyLiquidityValidationResult (v : PoolManagerImmutables) (f : Frame) (evm : State)
    (key : PoolKeyWords) : ExecResult :=
  if transientWord evm lockSlot = ⟨0⟩ then .reverted
  else if evm.executionEnv.codeOwner = v.original then
    if poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩ then .reverted
    else .ok (modifyLiquidityValidationFrame f key) evm
  else .reverted

theorem modifyLiquidityValidationSource {f : Frame} {evm : State} {key : PoolKeyWords}
    (v : PoolManagerImmutables) (hf : f.contract = contract) (him : f.immutables = immStore v)
    (hc : PoolKeyCanonical key) (hk : f.locals.get? "key" = some (poolKeyValue key)) :
    ExecBlock config f evm ((modifyLiquidityTransition.body.drop 7).take 8)
      (modifyLiquidityValidationResult v f evm key) := by
  have hlock := lockCall (evm := evm) hf "__c0"
  rw [modifyLiquidityValidationResult]
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    rw [decide_eq_false (not_not.mpr hl)] at hlock
    exact ExecBlock.consNormal hlock (ExecBlock.consRevert (ExecStmt.iteTrue
      (evalNotBool (va := false) (evalLocalValue (store_get_self _ _ _)))
      (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))
  rw [if_neg hl]
  rw [decide_eq_true hl] at hlock
  let f1 : Frame := {f with locals := f.locals.insert "__c0" (.bool true)}
  have hguard : ExecStmt config f1 evm modifyLiquidityTransition.body[8]! (.ok f1 evm) :=
    ExecStmt.iteFalse (evalNotBool (va := true) (evalLocalValue (store_get_self _ _ _))) ExecBlock.nil
  have hdelegate := noDelegateCallCall (f := f1) (evm := evm) v hf him "__c1"
  by_cases hd : evm.executionEnv.codeOwner = v.original
  swap
  · rw [if_neg hd] at hdelegate ⊢
    exact ExecBlock.consNormal hlock (ExecBlock.consNormal hguard (ExecBlock.consRevert hdelegate))
  rw [if_pos hd] at hdelegate ⊢
  let f2 : Frame := {f1 with locals := f1.locals.insert "__c1" .unit}
  let f3 : Frame := {f2 with locals := f2.locals.insert "id" (wordBytes32Value (poolKeyId key))}
  let f4 : Frame := {f3 with locals := f3.locals.insert "__c3" (poolRefValue (poolKeyId key))}
  let f5 : Frame := {f4 with locals := f4.locals.insert "pool" (poolRefValue (poolKeyId key))}
  let f6 : Frame := {f5 with locals := f5.locals.insert modifyLiquidityCheckAlias (poolRefValue (poolKeyId key))}
  have hid := poolIdCall (f := f2) (evm := evm) hf hc (evalLocalValue
    ((store_get_ne2 _ _ _ (by decide : ("__c0" == "key") = false)
      (by decide : ("__c1" == "key") = false)).trans hk)) "id"
  have hget := poolGetCall (f := f3) (evm := evm) hf (evalLocalValue (store_get_self _ _ _)) "__c3"
  have href : ExecStmt config f4 evm modifyLiquidityTransition.body[12]! (.ok f5 evm) :=
    ExecStmt.letStorage (resolveStorageAlias (store_get_self _ _ _))
  have halias : ExecStmt config f5 evm modifyLiquidityTransition.body[13]! (.ok f6 evm) :=
    ExecStmt.letStorage (resolveStorageAlias (store_get_self _ _ _))
  have hcheck := poolCheckCall (f := f6) (evm := evm) hf (evalLocalValue (store_get_self _ _ _)) "__c4"
  by_cases hp : poolSqrtPriceWord evm (poolKeyId key) = ⟨0⟩
  · rw [if_pos hp] at hcheck ⊢
    exact ExecBlock.consNormal hlock (ExecBlock.consNormal hguard (ExecBlock.consNormal hdelegate
      (ExecBlock.consNormal hid (ExecBlock.consNormal hget (ExecBlock.consNormal href
        (ExecBlock.consNormal halias (ExecBlock.consRevert hcheck)))))))
  · rw [if_neg hp] at hcheck ⊢
    exact ExecBlock.consNormal hlock (ExecBlock.consNormal hguard (ExecBlock.consNormal hdelegate
      (ExecBlock.consNormal hid (ExecBlock.consNormal hget (ExecBlock.consNormal href
        (ExecBlock.consNormal halias (execBlock_singleton hcheck)))))))

end Benchmarks.UniswapV4PoolManager
