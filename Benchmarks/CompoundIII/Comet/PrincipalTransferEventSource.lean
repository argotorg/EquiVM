import Benchmarks.CompoundIII.Comet.PresentValue
import Benchmarks.CompoundIII.Comet.TotalsStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def principalTransferEvent (mint : Bool) (accountName amountName retName : Ident) : Stmt :=
  .ite (.binary .gt (.var amountName) (.intLit 0))
    [.internalCall "presentValueSupply" [.storage ⟨"baseSupplyIndex", []⟩, .var amountName] retName,
      .emit "Transfer" (if mint then
        [.cast (.intLit 0) (.elem .address), .var accountName, .var retName] else
        [.var accountName, .cast (.intLit 0) (.elem .address), .var retName])] []

def principalTransferEventFrame (frame : Frame) (evm : EVM.State) (principal : UInt256)
    (retName : Ident) : Frame :=
  if 0 < principal.toNat then
    { frame with locals := frame.locals.insert retName (.int
      (presentValueWord (totalsIndexWord
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) false) principal).toNat) }
  else frame

theorem principalTransferEventFrame_contract (frame : Frame) (evm : EVM.State)
    (principal : UInt256) (retName : Ident) :
    (principalTransferEventFrame frame evm principal retName).contract = frame.contract := by
  unfold principalTransferEventFrame
  split <;> rfl

theorem principalTransferEventFrame_get (frame : Frame) (evm : EVM.State) (principal : UInt256)
    (retName key : Ident) (hne : retName ≠ key) :
    (principalTransferEventFrame frame evm principal retName).locals.get? key =
      frame.locals.get? key := by
  unfold principalTransferEventFrame
  split
  · simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, beq_iff_eq, hne, if_false]
  · rfl

theorem principalTransferEvent_source (frame : Frame) (evm : EVM.State) (mint : Bool)
    (account : AccountAddress) (principal : UInt256) (accountName amountName retName : Ident)
    (hne : retName ≠ accountName) (hc : frame.contract = contract)
    (ha : frame.locals.get? accountName = some (.address account))
    (hp : frame.locals.get? amountName = some (.int principal.toNat))
    (hi : frame.locals.get? "baseSupplyIndex" = none) (hb : principal.toNat < 2^104) :
    ExecStmt config frame evm (principalTransferEvent mint accountName amountName retName)
      (.ok (principalTransferEventFrame frame evm principal retName) evm) := by
  have he : evalExpr? config frame evm (.var amountName) = .ok (.int principal.toNat) := by
    simp only [evalExpr?, hp, EvalResult.ofOption]
  have hg : evalExpr? config frame evm (.binary .gt (.var amountName) (.intLit 0)) =
      .ok (.bool (decide (0 < principal.toNat))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, Int.natCast_pos]
  by_cases hpos : 0 < principal.toNat
  · let index := totalsIndexWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) false
    let value := presentValueWord index principal
    let final : Frame := { frame with locals := frame.locals.insert retName (.int value.toNat) }
    have hei : evalExpr? config frame evm (.storage ⟨"baseSupplyIndex", []⟩) =
        .ok (.int index.toNat) := by
      have heq : { frame with contract := contract } = frame := by rw [← hc]
      simpa only [heq, totalsIndexName, Bool.false_eq_true, if_false] using
        evalTotalsIndex evm frame.locals frame.immutables false hi
    have hcall := presentValue_call frame evm false index principal
      (.storage ⟨"baseSupplyIndex", []⟩) (.var amountName) retName hc
      (totalsIndexWord_lt _ false) hb hei he
    have haf : final.locals.get? accountName = some (.address account) := by
      simpa only [final, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_iff_eq, if_neg hne] using ha
    have hrf : final.locals.get? retName = some (.int value.toNat) := by
      simp only [final, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, if_true]
    have hem : ExecStmt config final evm (.emit "Transfer" (if mint then
        [.cast (.intLit 0) (.elem .address), .var accountName, .var retName] else
        [.var accountName, .cast (.intLit 0) (.elem .address), .var retName])) (.ok final evm) := by
      apply ExecStmt.emit (vals := if mint then
        [.address ⟨0, by decide⟩, .address account, .int value.toNat] else
        [.address account, .address ⟨0, by decide⟩, .int value.toNat])
      cases mint <;> simp only [Bool.false_eq_true, if_false, if_true, evalExprs?, evalExpr?,
        haf, hrf, pure, bind, EvalResult.bind, EvalResult.ofOption, castValue?] <;> rfl
    rw [principalTransferEventFrame, if_pos hpos]
    exact ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hpos]))
      (ExecBlock.consNormal hcall (ExecBlock.consNormal hem .nil))
  · rw [principalTransferEventFrame, if_neg hpos]
    exact ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hpos])) .nil

end Benchmarks.CompoundIII.Comet
