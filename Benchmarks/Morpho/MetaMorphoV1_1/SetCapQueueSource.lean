import Benchmarks.Morpho.MetaMorphoV1_1.SetCapSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayPush

/-! Withdrawal-queue length guards and the exact append performed when enabling a market. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def setCapQueueLength (evm : State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨21⟩

def setCapQueuePushState (evm : State) (id : UInt256) : State :=
  Solm.EVM.storageStore
    (Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨21⟩ (setCapQueueLength evm + ⟨1⟩))
    evm.executionEnv.codeOwner (solidityBytesDataBaseSlot ⟨21⟩ + setCapQueueLength evm) id

@[simp] theorem setCapQueuePushState_executionEnv (evm : State) (id : UInt256) :
    (setCapQueuePushState evm id).executionEnv = evm.executionEnv := by
  simp only [setCapQueuePushState, storageStore_executionEnv]

theorem setCapQueueConditionSource {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none)
    (limit : Nat) :
    evalExpr? config frame evm (setCapQueueCondition limit) =
      .ok (.bool (decide ((setCapQueueLength evm).toNat ≤ limit))) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hcontract
  subst c
  have hl := evalStorage_withdrawQueueLength evm locals imms hqueue
  simp only [setCapQueueCondition, evalExpr?, hl, bind, EvalResult.bind, evalBinaryOp?, pure,
    setCapQueueLength, Int.ofNat_eq_natCast]
  congr 3
  exact propext (by omega)

theorem setCapQueuePush {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id)) :
    ExecStmt config frame evm (.push ⟨"withdrawQueue", []⟩ (some (.var "id")))
      (.ok frame (setCapQueuePushState evm id)) := by
  have hr : resolveStorageRef? config frame evm ⟨"withdrawQueue", []⟩ =
      .ok (⟨"withdrawQueue", []⟩, .dynamicArray (.elem (.bytes abiBytes32Width))) := by
    apply resolveStorageRef?_ok hqueue
    · simp only [evalStorageRef, evalStorageRefSteps, bind, EvalResult.bind, pure]
    · rw [hcontract]; rfl
  apply ExecStmt.pushVal (value := wordBytes32Value id)
  · simp only [evalExpr?, hid, EvalResult.ofOption]
  simp only [pushArray?, usesTransientStorage_of_resolveStorageRef hr, Bool.false_eq_true,
    if_false, hr, bind, EvalResult.bind]
  change solidityPushStorage? stringStorageLayout ⟨"withdrawQueue", []⟩
    (.dynamicArray (.elem (.bytes abiBytes32Width))) (some (wordBytes32Value id)) evm = _
  have he := withdrawQueueElementLayout (setCapQueueLength evm).toNat
  rw [u256_ofNat_toNat] at he
  exact solidityPushWordArray evm (setCapQueueLength evm) id rfl rfl he

theorem setCapEnableBodyRevertsLength {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none)
    (hlen : ¬ (setCapQueueLength evm).toNat ≤ 2 ^ 64 - 1) :
    ExecBlock config frame evm setCapEnableBody .reverted := by
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  rw [setCapQueueConditionSource hcontract hqueue]
  exact congrArg (fun b ↦ EvalResult.ok (Value.bool b)) (decide_eq_false hlen)

theorem setCapEnableBodyPushStatic {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hlen : (setCapQueueLength evm).toNat ≤ 2 ^ 64 - 1)
    (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm setCapEnableBody .staticViolation := by
  have hg := setCapQueueConditionSource (evm := evm) hcontract hqueue (2 ^ 64 - 1)
  simp only [hlen, decide_true] at hg
  apply (ABlock.start.requireStep hg).run
  have hp := setCapQueuePush (evm := evm) hcontract hqueue hid
  cases hp with
  | pushVal he hs => exact ExecBlock.consStatic (ExecStmt.pushValStatic he hs hperm)

theorem setCapEnableBodyPushPrefix {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hlen : (setCapQueueLength evm).toNat ≤ 2 ^ 64 - 1)
    {result : ExecResult}
    (htail : ExecBlock config frame (setCapQueuePushState evm id)
      (setCapEnableBody.drop 2) result) :
    ExecBlock config frame evm setCapEnableBody result := by
  have hg := setCapQueueConditionSource (evm := evm) hcontract hqueue (2 ^ 64 - 1)
  simp only [hlen, decide_true] at hg
  apply (ABlock.start.requireStep hg).run
  exact ExecBlock.consNormal (setCapQueuePush hcontract hqueue hid) htail

theorem setCapEnableBodyRevertsFull {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hqueue : frame.locals.get? "withdrawQueue" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hlen : (setCapQueueLength evm).toNat ≤ 2 ^ 64 - 1)
    (hfull : ¬ (setCapQueueLength (setCapQueuePushState evm id)).toNat ≤ 30) :
    ExecBlock config frame evm setCapEnableBody .reverted := by
  apply setCapEnableBodyPushPrefix hcontract hqueue hid hlen
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hfull, decide_false] using setCapQueueConditionSource
    (evm := setCapQueuePushState evm id) hcontract hqueue 30

end Benchmarks.Morpho.MetaMorphoV1_1
