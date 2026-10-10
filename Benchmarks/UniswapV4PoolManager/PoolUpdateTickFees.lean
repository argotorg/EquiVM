import Benchmarks.UniswapV4PoolManager.TickStorage
import Benchmarks.UniswapV4PoolManager.PoolFeeGrowthStorage
import Benchmarks.UniswapV4PoolManager.Slot0TickSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev poolUpdateTickFunction : FunctionDecl := contract.functions[61]!
theorem poolUpdateTick_lookup : lookupCallable? contract "Pool_updateTick" =
    some poolUpdateTickFunction.toCallable := rfl

def tickFeeWrite0 (evm : EVM.State) (id : UInt256) (tick : Int) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ((tickSlot id tick)+⟨1⟩)
    (poolFeeGrowthWord evm id false)
def tickFeeWrites (evm : EVM.State) (id : UInt256) (tick : Int) : EVM.State :=
  let evm1 := tickFeeWrite0 evm id tick
  Solm.EVM.storageStore evm1 evm1.executionEnv.codeOwner ((tickSlot id tick)+⟨2⟩)
    (poolFeeGrowthWord evm1 id true)

def tickFeeWriteBody : List Stmt :=
  [.assign .storage {base := "info", steps := [.field "feeGrowthOutside0X128"]}
     (.storage {base := "self", steps := [.field "feeGrowthGlobal0X128"]}),
   .assign .storage {base := "info", steps := [.field "feeGrowthOutside1X128"]}
     (.storage {base := "self", steps := [.field "feeGrowthGlobal1X128"]})]

theorem tickFeeWriteSource {f : Frame} {evm : EVM.State} {id : UInt256} {tick : Int}
    (hs : f.locals.get? "self" = some (poolRefValue id))
    (hi : f.locals.get? "info" = some (tickRefValue id tick)) :
    ExecBlock config f evm tickFeeWriteBody
      (if evm.executionEnv.perm = false then .staticViolation else .ok f (tickFeeWrites evm id tick)) := by
  have h0 := poolFeeGrowth_read (evm := evm) hs false
  have hw0 := tickField_write (evm := evm) hi .feeGrowthOutside0 (poolFeeGrowthWord evm id false)
  by_cases hp : evm.executionEnv.perm = false
  · rw [if_pos hp]
    exact ExecBlock.consStatic (ExecStmt.assignStatic h0 hw0 hp)
  · rw [if_neg hp]
    exact ExecBlock.consNormal (ExecStmt.assign h0 hw0)
      (ExecBlock.consNormal (ExecStmt.assign (poolFeeGrowth_read (evm := tickFeeWrite0 evm id tick) hs true)
        (tickField_write hi .feeGrowthOutside1 (poolFeeGrowthWord (tickFeeWrite0 evm id tick) id true))) ExecBlock.nil)

def tickFeeFrame (f : Frame) (evm : EVM.State) (id : UInt256) (gross : Int) : Frame :=
  if gross = 0 then {f with locals := f.locals.insert "__c1" (.int (EVM.signed (slot0TickWord (poolSlot0Word evm id))))}
  else f
def tickFeesNeeded (evm : EVM.State) (id : UInt256) (tick gross : Int) : Prop :=
  gross = 0 ∧ tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id))
instance (evm : EVM.State) (id : UInt256) (tick gross : Int) : Decidable (tickFeesNeeded evm id tick gross) :=
  inferInstanceAs (Decidable (_ ∧ _))
def tickFeeResult (f : Frame) (evm : EVM.State) (id : UInt256) (tick gross : Int) : ExecResult :=
  if tickFeesNeeded evm id tick gross then
    if evm.executionEnv.perm = false then .staticViolation else .ok (tickFeeFrame f evm id gross) (tickFeeWrites evm id tick)
  else .ok (tickFeeFrame f evm id gross) evm

theorem poolUpdateTickFees {f : Frame} {evm : EVM.State} {id : UInt256} {tick gross : Int}
    (hf : f.contract = contract) (hs : f.locals.get? "self" = some (poolRefValue id))
    (hi : f.locals.get? "info" = some (tickRefValue id tick))
    (ht : f.locals.get? "tick" = some (.int tick))
    (hg : f.locals.get? "liquidityGrossBefore" = some (.int gross)) :
    ExecStmt config f evm poolUpdateTickFunction.body[9]! (tickFeeResult f evm id tick gross) := by
  have hzero := evalIntEq (evalLocalValue (cfg := config) (evm := evm) hg)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int 0) by simp only [evalExpr?, pure])
  by_cases hz : gross = 0
  · let f1 : Frame := {f with locals := f.locals.insert "__c1" (.int (EVM.signed (slot0TickWord (poolSlot0Word evm id))))}
    have hcall : ExecStmt config f evm (.internalCall "Slot0Library_tick"
        [.storage {base := "self", steps := [.field "slot0"]}] "__c1") (.ok f1 evm) :=
      slot0TickCall hf (poolSlot0_read hs) "__c1"
    have hcmp : evalExpr? config f1 evm (.binary .le (.var "tick") (.var "__c1")) =
        .ok (.bool (decide (tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id))))) := by
      rw [evalExpr_binary_nonshort (by decide) (by decide), evalLocalValue
        ((store_get_ne _ _ (by decide : ("__c1" == "tick") = false)).trans ht),
        evalLocalValue (store_get_self _ _ _)]
      rfl
    by_cases hc : tick ≤ EVM.signed (slot0TickWord (poolSlot0Word evm id))
    · have hb := tickFeeWriteSource (f := f1) (evm := evm)
        ((store_get_ne _ _ (by decide : ("__c1" == "self") = false)).trans hs)
        ((store_get_ne _ _ (by decide : ("__c1" == "info") = false)).trans hi)
      simp only [tickFeeResult, tickFeesNeeded, hz, hc, and_self, if_true, tickFeeFrame]
      apply ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hzero)
      apply ExecBlock.consNormal hcall
      by_cases hp : evm.executionEnv.perm = false
      · rw [if_pos hp] at hb ⊢
        exact ExecBlock.consStatic (ExecStmt.iteTrue (by simpa only [decide_eq_true hc] using hcmp) hb)
      · rw [if_neg hp] at hb ⊢
        exact ExecBlock.consNormal (ExecStmt.iteTrue (by simpa only [decide_eq_true hc] using hcmp) hb) ExecBlock.nil
    · simp only [tickFeeResult, tickFeesNeeded, hz, hc, and_false, if_false, tickFeeFrame, if_true]
      exact ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using hzero)
        (ExecBlock.consNormal hcall (ExecBlock.consNormal
          (ExecStmt.iteFalse (by simpa only [decide_eq_false hc] using hcmp) ExecBlock.nil) ExecBlock.nil))
  · simp only [tickFeeResult, tickFeesNeeded, hz, false_and, if_false, tickFeeFrame]
    exact ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using hzero) ExecBlock.nil

theorem tickFeeFrame_get {f : Frame} {evm : EVM.State} {id : UInt256} {gross : Int} {name : Ident}
    (hn : ("__c1" == name) = false) :
    (tickFeeFrame f evm id gross).locals.get? name = f.locals.get? name := by
  unfold tickFeeFrame
  split
  · exact store_get_ne _ _ hn
  · rfl

end Benchmarks.UniswapV4PoolManager
