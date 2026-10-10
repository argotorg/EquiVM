import Benchmarks.UniswapV4PoolManager.PoolProtocolFeeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def setProtocolFeeAlias : Ident := "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.29"
def setProtocolFeeFinalFrame (f : Frame) (key : PoolKeyWords) (fee : UInt256) : Frame :=
  let locals := f.locals.insert "key" (poolKeyValue key)
  let locals := locals.insert "__c0" (.bool (decide (protocolFeeValid fee)))
  let locals := locals.insert "id" (wordBytes32Value (poolKeyId key))
  let locals := locals.insert "__c2" (poolRefValue (poolKeyId key))
  let locals := locals.insert setProtocolFeeAlias (poolRefValue (poolKeyId key))
  {f with locals := locals.insert "__c3" .unit}

def setProtocolFeeResult (f : Frame) (evm : EVM.State) (key : PoolKeyWords) (fee : UInt256) : ExecResult :=
  if protocolControllerAuthorized evm then
    if protocolFeeValid fee then poolSetProtocolResult (setProtocolFeeFinalFrame f key fee) evm (poolKeyId key) fee
    else .reverted
  else .reverted

theorem setProtocolFeeTail {f : Frame} {evm : EVM.State} {id fee : UInt256}
    (hf : f.contract = contract) (hc : fee.toNat < 2^24)
    (hr : f.locals.get? setProtocolFeeAlias = some (poolRefValue id))
    (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (he : f.locals.get? "newProtocolFee" = some (.int (Int.ofNat fee.toNat))) :
    ExecFuncBody config f evm (setProtocolFeeTransition.body.drop 10)
      (poolSetProtocolResult {f with locals := f.locals.insert "__c3" .unit} evm id fee) := by
  have hset := poolSetProtocolCall (evm := evm) hf hc (evalLocalValue hr) (evalLocalValue he) "__c3"
  simp only [poolSetProtocolCallResult, poolSetProtocolResult, poolSetSlot0Result, resumeCallResult_ite,
    resumeCallResult_reverted, resumeCallResult_static, resumeCallResult_returned] at hset ⊢
  by_cases hz : poolSqrtPriceWord evm id = ⟨0⟩
  · rw [if_pos hz] at hset ⊢
    exact .execBlockRevert (ExecBlock.consRevert hset)
  · rw [if_neg hz] at hset ⊢
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp] at hset ⊢
      exact .execBlockStatic (ExecBlock.consStatic hset)
    · rw [if_neg hp] at hset ⊢
      apply ExecFuncBody.execBlockOK
      refine ExecBlock.consNormal hset (ExecBlock.consNormal
        (ExecStmt.emit (vals := [wordBytes32Value id, .int (Int.ofNat fee.toNat)]) ?_) ExecBlock.nil)
      have hi' := evalLocalValue (cfg := config) (f := {f with locals := f.locals.insert "__c3" .unit})
        (evm := poolSetProtocolPost evm id fee)
        ((store_get_ne _ _ (by decide : ("__c3" == "id") = false)).trans hi)
      have he' := evalLocalValue (cfg := config) (f := {f with locals := f.locals.insert "__c3" .unit})
        (evm := poolSetProtocolPost evm id fee)
        ((store_get_ne _ _ (by decide : ("__c3" == "newProtocolFee") = false)).trans he)
      change evalExprs? config {f with locals := f.locals.insert "__c3" .unit}
        (poolSetProtocolPost evm id fee) [.var "id", .var "newProtocolFee"] =
          .ok [wordBytes32Value id, .int (Int.ofNat fee.toNat)]
      simp only [evalExprs?, hi', he', bind, EvalResult.bind, pure]

theorem setProtocolFeeBody {evm : EVM.State} {locals imms : Store} {key : PoolKeyWords} {fee : UInt256}
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hc : PoolKeyCanonical key) (hfee : fee.toNat < 2^24)
    (hk : locals.get? "key" = some (.tuple (poolKeyValues key)))
    (he : locals.get? "newProtocolFee" = some (.int (Int.ofNat fee.toNat)))
    (hb : locals.get? "protocolFeeController" = none) :
    ExecTransitionBody config contract evm locals setProtocolFeeTransition.body
      (setProtocolFeeResult (calldataFrame contract locals imms evm) evm key fee) imms := by
  let f := calldataFrame contract locals imms evm
  let f1 : Frame := {f with locals := f.locals.insert "key" (poolKeyValue key)}
  let f2 : Frame := {f1 with locals := f1.locals.insert "__c0" (.bool (decide (protocolFeeValid fee)))}
  let f3 : Frame := {f2 with locals := f2.locals.insert "id" (wordBytes32Value (poolKeyId key))}
  let f4 : Frame := {f3 with locals := f3.locals.insert "__c2" (poolRefValue (poolKeyId key))}
  let f5 : Frame := {f4 with locals := f4.locals.insert setProtocolFeeAlias (poolRefValue (poolKeyId key))}
  have hlet : ExecStmt config f evm setProtocolFeeTransition.body[3]! (.ok f1 evm) :=
    ExecStmt.letDecl (poolKeyFromTuple_eval (evalLocalValue
      ((store_get_ne _ _ (by decide : ("__calldata" == "key") = false)).trans hk)))
  have hguard := protocolControllerGuard (f := f1) (evm := evm) rfl
    ((store_get_ne2 _ _ _ (by decide : ("__calldata" == "protocolFeeController") = false)
      (by decide : ("key" == "protocolFeeController") = false)).trans hb)
  rw [setProtocolFeeResult]
  by_cases hauth : protocolControllerAuthorized evm
  · rw [if_pos hauth]
    rw [decide_eq_false (not_not.mpr hauth)] at hguard
    have hite : ExecStmt config f1 evm setProtocolFeeTransition.body[4]! (.ok f1 evm) :=
      ExecStmt.iteFalse hguard ExecBlock.nil
    have he1 : f1.locals.get? "newProtocolFee" = some (.int (Int.ofNat fee.toNat)) :=
      (store_get_ne2 _ _ _ (by decide : ("__calldata" == "newProtocolFee") = false)
        (by decide : ("key" == "newProtocolFee") = false)).trans he
    have hvalid := protocolFeeValidCall (f := f1) (evm := evm) rfl hfee (evalLocalValue he1) "__c0"
    have hvguard := evalNotBool (evalLocalValue (cfg := config) (f := f2) (evm := evm) (store_get_self _ _ _))
    by_cases hv : protocolFeeValid fee
    · rw [if_pos hv]
      have hvg : evalExpr? config f2 evm (.unary .not (.var "__c0")) = .ok (.bool false) := by
        simpa only [decide_eq_true hv, Bool.not_true] using hvguard
      have hvite : ExecStmt config f2 evm setProtocolFeeTransition.body[6]! (.ok f2 evm) :=
        ExecStmt.iteFalse hvg ExecBlock.nil
      have hid := poolIdCall (f := f2) (evm := evm) rfl hc (evalLocalValue
        ((store_get_ne _ _ (by decide : ("__c0" == "key") = false)).trans (store_get_self _ _ _))) "id"
      have hget := poolGetCall (f := f3) (evm := evm) rfl (evalLocalValue (store_get_self _ _ _)) "__c2"
      have href : ExecStmt config f4 evm setProtocolFeeTransition.body[9]! (.ok f5 evm) :=
        ExecStmt.letStorage (resolveStorageAlias (store_get_self _ _ _))
      have hi5 : f5.locals.get? "id" = some (wordBytes32Value (poolKeyId key)) :=
        (store_get_ne2 _ _ _ (by decide : ("__c2" == "id") = false)
          (by decide : (setProtocolFeeAlias == "id") = false)).trans (store_get_self _ _ _)
      have he5 : f5.locals.get? "newProtocolFee" = some (.int (Int.ofNat fee.toNat)) :=
        (store_get_ne4 _ _ _ _ _ (by decide : ("__c0" == "newProtocolFee") = false)
          (by decide : ("id" == "newProtocolFee") = false) (by decide : ("__c2" == "newProtocolFee") = false)
          (by decide : (setProtocolFeeAlias == "newProtocolFee") = false)).trans he1
      have htail := setProtocolFeeTail (f := f5) (evm := evm) rfl hfee (store_get_self _ _ _) hi5 he5
      apply nonpayableCalldataBody hwv hhi
      exact execFuncBody_prepend
        (ExecBlock.consNormal hlet (ExecBlock.consNormal hite (ExecBlock.consNormal hvalid
          (ExecBlock.consNormal hvite (ExecBlock.consNormal hid (ExecBlock.consNormal hget
            (ExecBlock.consNormal href ExecBlock.nil))))))) htail
    · rw [if_neg hv]
      have hvg : evalExpr? config f2 evm (.unary .not (.var "__c0")) = .ok (.bool true) := by
        simpa only [decide_eq_false hv, Bool.not_false] using hvguard
      apply ExecFuncBody.execBlockRevert
      apply nonpayableCalldataBlock hwv hhi
      exact ExecBlock.consNormal hlet (ExecBlock.consNormal hite (ExecBlock.consNormal hvalid (ExecBlock.consRevert
        (ExecStmt.iteTrue hvg (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))
  · rw [if_neg hauth]
    rw [decide_eq_true hauth] at hguard
    apply ExecFuncBody.execBlockRevert
    apply nonpayableCalldataBlock hwv hhi
    exact ExecBlock.consNormal hlet (ExecBlock.consRevert
      (ExecStmt.iteTrue hguard (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))

end Benchmarks.UniswapV4PoolManager
