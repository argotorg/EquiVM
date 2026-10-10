import Benchmarks.UniswapV4PoolManager.UnlockABI
import Benchmarks.UniswapV4PoolManager.LockSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def unlockPrefixFrame (f : Frame) (caller : AccountAddress) : Frame :=
  {f with locals := ((((f.locals.insert "result" (.bytes .empty)).insert "__c0" (.bool false)).insert
    "__c1" .unit).insert "caller" (.address caller))}

theorem unlockPrefix {f : Frame} {evm : EVM.State} (hf : f.contract = contract) :
    ExecBlock config f evm (unlockTransition.body.drop 3 |>.take 5)
      (if transientWord evm lockSlot = ⟨0⟩ then
        if evm.executionEnv.perm = false then .staticViolation else
          .ok (unlockPrefixFrame f evm.executionEnv.source) (lockSetPost evm true)
       else .reverted) := by
  let f1 : Frame := {f with locals := f.locals.insert "result" (.bytes .empty)}
  have hlet : ExecStmt config f evm unlockTransition.body[3]! (.ok f1 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, bind, EvalResult.bind, pure]; rfl)
  have hlock := lockCall (f := f1) (evm := evm) hf "__c0"
  by_cases hl : transientWord evm lockSlot = ⟨0⟩
  · rw [if_pos hl]
    rw [decide_eq_false (not_not.mpr hl)] at hlock
    let f2 : Frame := {f1 with locals := f1.locals.insert "__c0" (.bool false)}
    have hguard : ExecStmt config f2 evm unlockTransition.body[5]! (.ok f2 evm) :=
      ExecStmt.iteFalse (evalLocalValue (store_get_self _ _ _)) ExecBlock.nil
    have hopen := lockSetCall (f := f2) (evm := evm) hf true "__c1"
    by_cases hp : evm.executionEnv.perm = false
    · rw [if_pos hp] at hopen ⊢
      exact ExecBlock.consNormal hlet (ExecBlock.consNormal hlock
        (ExecBlock.consNormal hguard (ExecBlock.consStatic hopen)))
    · rw [if_neg hp] at hopen ⊢
      exact ExecBlock.consNormal hlet (ExecBlock.consNormal hlock (ExecBlock.consNormal hguard
        (ExecBlock.consNormal hopen (ExecBlock.consNormal
          (ExecStmt.letDecl (by simp only [evalExpr?, envValue, pure, lockSetPost,
            transientStore_executionEnv])) ExecBlock.nil))))
  · rw [if_neg hl]
    rw [decide_eq_true hl] at hlock
    exact ExecBlock.consNormal hlet (ExecBlock.consNormal hlock (ExecBlock.consRevert
      (ExecStmt.iteTrue (evalLocalValue (store_get_self _ _ _))
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure]))))))

def unlockReturnFrame (f : Frame) (data : ByteArray) : Frame :=
  {f with locals := (((f.locals.insert "result" (.bytes data)).insert "__c3" (.int 0)).insert "__c4" .unit)}

def unlockAfterCallbackResult (f : Frame) (evm : EVM.State) (data : ByteArray) : ExecResult :=
  if transientWord evm deltaCountSlot = ⟨0⟩ then
    .returned (unlockReturnFrame f data) (lockSetPost evm false) (some [.bytes data])
  else .reverted

theorem unlockAfterCallback {f : Frame} {evm : EVM.State} {data old : ByteArray}
    (hf : f.contract = contract) (hp : evm.executionEnv.perm = true)
    (hc : f.locals.get? "__c2" = some (.bytes data))
    (hr : f.locals.get? "result" = some (.bytes old)) :
    ExecFuncBody config f evm (unlockTransition.body.drop 9) (unlockAfterCallbackResult f evm data) := by
  let f1 : Frame := {f with locals := f.locals.insert "result" (.bytes data)}
  have hassign : ExecStmt config f evm unlockTransition.body[9]! (.ok f1 evm) :=
    ExecStmt.assign (evalLocalValue hc) (assignLocalValue hr)
  have hcount := deltaCountReadCall (f := f1) (evm := evm) hf "__c3"
  let f2 : Frame := {f1 with locals := f1.locals.insert "__c3" (.int (Int.ofNat (transientWord evm deltaCountSlot).toNat))}
  have hcond : evalExpr? config f2 evm (.binary .ne (.var "__c3") (.intLit 0)) =
      .ok (.bool (decide (transientWord evm deltaCountSlot ≠ ⟨0⟩))) :=
    evalNeWords (evalLocalValue (store_get_self _ _ _)) (by simp only [evalExpr?, pure]; rfl)
  unfold unlockAfterCallbackResult
  by_cases hz : transientWord evm deltaCountSlot = ⟨0⟩
  · rw [if_pos hz]
    rw [decide_eq_false (not_not.mpr hz)] at hcond
    have hguard : ExecStmt config f2 evm unlockTransition.body[11]! (.ok f2 evm) :=
      ExecStmt.iteFalse hcond ExecBlock.nil
    have hclose := lockSetCall (f := f2) (evm := evm) hf false "__c4"
    rw [if_neg (by rw [hp]; decide)] at hclose
    have hret : evalExpr? config {f2 with locals := f2.locals.insert "__c4" .unit}
        (lockSetPost evm false) (.var "result") = .ok (.bytes data) :=
      evalLocalValue ((store_get_ne _ _ (by decide : ("__c4" == "result") = false)).trans
        ((store_get_ne _ _ (by decide : ("__c3" == "result") = false)).trans (store_get_self _ _ _)))
    have hh := ExecFuncBody.execBlockRet (ExecBlock.consNormal hassign (ExecBlock.consNormal hcount
      (ExecBlock.consNormal hguard (ExecBlock.consNormal hclose (ABlock.start.returns (rest := []) hret)))))
    simpa only [f1, f2, hz, unlockReturnFrame] using hh
  · rw [if_neg hz]
    rw [decide_eq_true hz] at hcond
    exact .execBlockRevert (ExecBlock.consNormal hassign (ExecBlock.consNormal hcount
      (ExecBlock.consRevert (ExecStmt.iteTrue hcond
        (ExecBlock.consRevert (ExecStmt.requireFalse (by simp only [evalExpr?, pure])))))))

def unlockCallbackResult (f : Frame) (evm : EVM.State) (z : Bool) (out : ByteArray) : ExecResult :=
  if z = true ∧ BytesReturnBounds out then
    unlockAfterCallbackResult {f with locals := f.locals.insert "__c2" (.bytes (bytesReturnPayload out))}
      evm (bytesReturnPayload out)
  else .reverted

theorem unlockCallbackBody {f : Frame} {evm evm' : EVM.State} {data old out : ByteArray}
    {caller : AccountAddress} {z : Bool} (hf : f.contract = contract) (hp : evm'.executionEnv.perm = true)
    (hc : f.locals.get? "caller" = some (.address caller))
    (hd : f.locals.get? "data" = some (.bytes data))
    (hr : f.locals.get? "result" = some (.bytes old))
    (hcall : typedCallViaEVM config evm caller "unlockCallback" 0 [.bytes data] (z, evm', out) true) :
    ExecFuncBody config f evm (unlockTransition.body.drop 8) (unlockCallbackResult f evm' z out) := by
  have hargs := evalExprs?_singleton (evalLocalValue (cfg := config) (evm := evm) hd)
  have heth : evalExpr? config f evm (.intLit 0) = .ok (.int 0) := by simp only [evalExpr?, pure]
  have hcall' : typedCallViaEVM config evm (EVM.address caller) "unlockCallback" 0
      [.bytes data] (z, evm', out) true := by simpa only [address_of_val] using hcall
  unfold unlockCallbackResult
  cases z with
  | false =>
    rw [if_neg (by simp)]
    exact .execBlockRevert (ExecBlock.consRevert
      (ExecStmt.externalCallFailure (evalLocalValue hc) heth hargs hcall'))
  | true =>
    by_cases hb : BytesReturnBounds out
    · rw [if_pos ⟨rfl, hb⟩]
      have hstmt := ExecStmt.externalCallSuccess (retVar := "__c2") (evalLocalValue hc) heth hargs hcall'
        (unlockCallbackDecode_ok hb)
      have hbody := unlockAfterCallback (f := {f with locals := f.locals.insert "__c2" (.bytes (bytesReturnPayload out))})
        hf hp (store_get_self _ _ _)
        ((store_get_ne _ _ (by decide : ("__c2" == "result") = false)).trans hr)
      exact execFuncBody_prepend (execBlock_singleton hstmt) hbody
    · rw [if_neg (fun h => hb h.2)]
      exact .execBlockRevert (ExecBlock.consRevert (ExecStmt.externalCallReturnDecodeRevert
        (evalLocalValue hc) heth hargs hcall' (unlockCallbackDecode_none hb)))

end Benchmarks.UniswapV4PoolManager
