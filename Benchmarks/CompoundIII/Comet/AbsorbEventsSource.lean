import Benchmarks.CompoundIII.Comet.PrincipalTransferEventSource
import Benchmarks.CompoundIII.Comet.Unsigned104

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbEventsBlock : List Stmt :=
  [.emit "AbsorbDebt" [.var "absorber", .var "account", .var "basePaidOut", .var "valueOfBasePaidOut"],
    .ite (.binary .gt (.var "newPrincipal") (.intLit 0))
      [.internalCall "unsigned104" [.var "newPrincipal"] "__c15",
        .internalCall "presentValueSupply" [.storage ⟨"baseSupplyIndex", []⟩, .var "__c15"] "__c16",
        .emit "Transfer" [.cast (.intLit 0) (.elem .address), .var "account", .var "__c16"]] []]

theorem absorbEvents_source (frame : Frame) (evm : State) (absorber account : AccountAddress)
    (paid value principal : UInt256) (hc : frame.contract = contract)
    (ha : frame.locals.get? "absorber" = some (.address absorber))
    (hb : frame.locals.get? "account" = some (.address account))
    (hp : frame.locals.get? "basePaidOut" = some (.int paid.toNat))
    (hv : frame.locals.get? "valueOfBasePaidOut" = some (.int value.toNat))
    (hn : frame.locals.get? "newPrincipal" = some (.int principal.toNat))
    (hi : frame.locals.get? "baseSupplyIndex" = none) (hbound : principal.toNat < 2^104) :
    ∃ frame', ExecBlock config frame evm absorbEventsBlock (.ok frame' evm) := by
  have hd : ExecStmt config frame evm
      (.emit "AbsorbDebt" [.var "absorber", .var "account", .var "basePaidOut", .var "valueOfBasePaidOut"])
      (.ok frame evm) := by
    apply ExecStmt.emit (vals := [.address absorber, .address account, .int paid.toNat, .int value.toNat])
    simp only [evalExprs?, evalExpr?, ha, hb, hp, hv, EvalResult.ofOption, pure, bind, EvalResult.bind]
  have he : evalExpr? config frame evm (.var "newPrincipal") = .ok (.int principal.toNat) := by
    simp only [evalExpr?, hn, EvalResult.ofOption]
  have hg : evalExpr? config frame evm (.binary .gt (.var "newPrincipal") (.intLit 0)) =
      .ok (.bool (decide (0 < principal.toNat))) := by
    simp only [evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?, Int.natCast_pos]
  by_cases hpos : 0 < principal.toNat
  · have hu := unsigned104_call frame evm principal (.var "newPrincipal") "__c15" hc he hbound
    let f1 : Frame := { frame with locals := frame.locals.insert "__c15" (.int principal.toNat) }
    let index := totalsIndexWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩) false
    have hi1 : f1.locals.get? "baseSupplyIndex" = none := by
      simpa only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hi
    have hei : evalExpr? config f1 evm (.storage ⟨"baseSupplyIndex", []⟩) =
        .ok (.int index.toNat) := by
      simpa only [← hc] using evalTotalsIndex evm f1.locals f1.immutables false hi1
    have hep : evalExpr? config f1 evm (.var "__c15") = .ok (.int principal.toNat) := by
      simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]; rfl
    have hcall := presentValue_call f1 evm false index principal
      (.storage ⟨"baseSupplyIndex", []⟩) (.var "__c15") "__c16" hc
      (totalsIndexWord_lt _ false) hbound hei hep
    let f2 : Frame := { f1 with
      locals := f1.locals.insert "__c16" (.int (presentValueWord index principal).toNat) }
    have ha2 : f2.locals.get? "account" = some (.address account) := by
      simpa only [f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hb
    have hv2 : f2.locals.get? "__c16" = some (.int (presentValueWord index principal).toNat) := by
      simp only [f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl
    have hem : ExecStmt config f2 evm
        (.emit "Transfer" [.cast (.intLit 0) (.elem .address), .var "account", .var "__c16"])
        (.ok f2 evm) := by
      apply ExecStmt.emit (vals := [.address ⟨0, by decide⟩, .address account,
        .int (presentValueWord index principal).toNat])
      simp only [evalExprs?, evalExpr?, ha2, hv2, pure, bind, EvalResult.bind,
        EvalResult.ofOption, castValue?]; rfl
    exact ⟨f2, ExecBlock.consNormal hd (ExecBlock.consNormal
      (ExecStmt.iteTrue (hg.trans (by rw [decide_eq_true hpos]))
        (ExecBlock.consNormal hu (ExecBlock.consNormal hcall (ExecBlock.consNormal hem .nil)))) .nil)⟩
  · exact ⟨frame, ExecBlock.consNormal hd (ExecBlock.consNormal
      (ExecStmt.iteFalse (hg.trans (by rw [decide_eq_false hpos])) .nil) .nil)⟩

end Benchmarks.CompoundIII.Comet
