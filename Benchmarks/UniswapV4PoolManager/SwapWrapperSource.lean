import Benchmarks.UniswapV4PoolManager.SwapWrapperEventSource
import Benchmarks.UniswapV4PoolManager.ProtocolFeesUpdateSource
import Benchmarks.UniswapV4PoolManager.PoolSwapFinishSource
import Benchmarks.UniswapV4PoolManager.LocalBytes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def swapWrapperAlias : Ident :=
  "__solm_storage_ref._@.Benchmarks.UniswapV4PoolManager.SpecSyntax.2010301240._hygCtx._hyg.15"

def swapWrapperUnpackFrame (f : Frame) (delta fee amount : UInt256) (r : PoolSwapResultWords) : Frame :=
  valueLocal (wordLocal (wordLocal (valueLocal f "delta" (.int (EVM.signed delta)))
    "amountToProtocol" amount) "swapFee" fee) "result" (poolSwapResultValue r)

theorem swapWrapperUnpack_contract (f : Frame) (delta fee amount : UInt256) (r : PoolSwapResultWords) :
    (swapWrapperUnpackFrame f delta fee amount r).contract = f.contract := by
  simp only [swapWrapperUnpackFrame, valueLocal_contract, wordLocal_contract]

theorem swapWrapperUnpack_get (f : Frame) (delta fee amount : UInt256) (r : PoolSwapResultWords)
    (name : Ident) (hd : name ≠ "delta") (ha : name ≠ "amountToProtocol")
    (he : name ≠ "swapFee") (hr : name ≠ "result") :
    (swapWrapperUnpackFrame f delta fee amount r).locals.get? name = f.locals.get? name := by
  simp only [swapWrapperUnpackFrame, valueLocal_get, wordLocal_get, beq_iff_eq,
    Ne.symm hd, Ne.symm ha, Ne.symm he, Ne.symm hr, if_false]

theorem swapWrapperUnpackSource {f : Frame} {evm : State} {delta fee amount : UInt256} {r : PoolSwapResultWords}
    (hv : f.locals.get? "__c0" = some (.tuple (poolSwapReturnValues delta fee amount r))) :
    ExecBlock config f evm ((swapWrapperFunction.body.drop 2).take 4)
      (.ok (swapWrapperUnpackFrame f delta fee amount r) evm) := by
  let f1 := valueLocal f "delta" (.int (EVM.signed delta))
  let f2 := wordLocal f1 "amountToProtocol" amount
  let f3 := wordLocal f2 "swapFee" fee
  have hv1 : f1.locals.get? "__c0" = some (.tuple (poolSwapReturnValues delta fee amount r)) :=
    (store_get_ne _ _ (by decide : ("delta" == "__c0") = false)).trans hv
  have hv2 : f2.locals.get? "__c0" = some (.tuple (poolSwapReturnValues delta fee amount r)) :=
    (store_get_ne _ _ (by decide : ("amountToProtocol" == "__c0") = false)).trans hv1
  have hv3 : f3.locals.get? "__c0" = some (.tuple (poolSwapReturnValues delta fee amount r)) :=
    (store_get_ne _ _ (by decide : ("swapFee" == "__c0") = false)).trans hv2
  exact ExecBlock.consNormal (ExecStmt.letDecl (evalTupleProjection (evalLocalValue hv) (i := 0) rfl))
    (ExecBlock.consNormal (ExecStmt.letDecl (evalTupleProjection (evalLocalValue hv1) (i := 1) rfl))
      (ExecBlock.consNormal (ExecStmt.letDecl (evalTupleProjection (evalLocalValue hv2) (i := 2) rfl))
        (execBlock_singleton (ExecStmt.letDecl (evalTupleProjection (evalLocalValue hv3) (i := 3) rfl)))))

def swapWrapperFeeFrame (f : Frame) (amount : UInt256) : Frame :=
  if 0 < amount.toNat then valueLocal f "__c1" .unit else f

def swapWrapperFeePost (evm : State) (currency : AccountAddress) (amount : UInt256) : State :=
  if 0 < amount.toNat then protocolFeesUpdatePost evm currency amount else evm

theorem swapWrapperFeePost_executionEnv (evm : State) (currency : AccountAddress) (amount : UInt256) :
    (swapWrapperFeePost evm currency amount).executionEnv = evm.executionEnv := by
  unfold swapWrapperFeePost
  split
  · exact storageStore_executionEnv ..
  · rfl

theorem swapWrapperFeePost_σ₀ (evm : State) (currency : AccountAddress) (amount : UInt256) :
    (swapWrapperFeePost evm currency amount).σ₀ = evm.σ₀ := by
  unfold swapWrapperFeePost
  split
  · exact storageStore_σ₀ ..
  · rfl

def swapWrapperTailResult (f : Frame) (evm : State) (currency : AccountAddress) (delta amount : UInt256) : ExecResult :=
  if evm.executionEnv.perm = false then .staticViolation else
    .returned (swapWrapperEventFrame (swapWrapperFeeFrame f amount) delta)
      (swapWrapperFeePost evm currency amount) (some [.int (EVM.signed delta)])

theorem swapWrapperTailSource {f : Frame} {evm : State} {id delta fee amount : UInt256}
    {currency : AccountAddress} {r : PoolSwapResultWords}
    (hf : f.contract = contract) (hi : f.locals.get? "id" = some (wordBytes32Value id))
    (hd : f.locals.get? "delta" = some (.int (EVM.signed delta)))
    (he : f.locals.get? "swapFee" = some (.int (Int.ofNat fee.toNat)))
    (ha : f.locals.get? "amountToProtocol" = some (.int (Int.ofNat amount.toNat)))
    (hr : f.locals.get? "result" = some (poolSwapResultValue r))
    (hc : f.locals.get? "inputCurrency" = some (.address currency)) :
    ExecFuncBody config f evm (swapWrapperFunction.body.drop 6)
      (swapWrapperTailResult f evm currency delta amount) := by
  have hcond := evalNatGtLiteral (cfg := config) (evm := evm) (k := 0) (evalLocalValue ha)
  by_cases hz : 0 < amount.toNat
  · rw [decide_eq_true hz] at hcond
    have hcall := protocolFeesUpdateCall (evm := evm) hf (evalLocalValue hc) (evalLocalValue ha) "__c1"
    by_cases hp : evm.executionEnv.perm = false
    · simp only [protocolFeesUpdateResult, if_pos hp, resumeCallResult_static] at hcall
      simp only [swapWrapperTailResult, if_pos hp]
      exact .execBlockStatic (ExecBlock.consStatic
        (ExecStmt.iteTrue hcond (ExecBlock.consStatic hcall)))
    · simp only [protocolFeesUpdateResult, if_neg hp, resumeCallResult_returned] at hcall
      let f1 := valueLocal f "__c1" .unit
      have hget (name : Ident) (hn : ("__c1" == name) = false) :
          f1.locals.get? name = f.locals.get? name := store_get_ne _ _ hn
      have htail := swapWrapperEventSource (f := f1) (evm := protocolFeesUpdatePost evm currency amount) hf
        ((hget "id" (by decide)).trans hi) ((hget "delta" (by decide)).trans hd)
        ((hget "swapFee" (by decide)).trans he) ((hget "result" (by decide)).trans hr)
      simp only [protocolFeesUpdatePost, protocolFeesPost, storageStore_executionEnv, if_neg hp] at htail
      simpa only [swapWrapperTailResult, if_neg hp, swapWrapperFeeFrame, swapWrapperFeePost, if_pos hz] using
        execFuncBody_prepend (execBlock_singleton (ExecStmt.iteTrue hcond (execBlock_singleton hcall))) htail
  · rw [decide_eq_false hz] at hcond
    have htail := swapWrapperEventSource (evm := evm) hf hi hd he hr
    simpa only [swapWrapperTailResult, swapWrapperFeeFrame, swapWrapperFeePost, if_neg hz] using
      execFuncBody_prepend (execBlock_singleton (ExecStmt.iteFalse hcond ExecBlock.nil)) htail

end Benchmarks.UniswapV4PoolManager
