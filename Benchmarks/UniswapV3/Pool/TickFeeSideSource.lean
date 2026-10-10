import Benchmarks.UniswapV3.Pool.TickFeeModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickFeeSideFrame (frame : Frame) (a : TickFeeArgs) (evm : EVM.State)
    (above : Bool) : Frame :=
  let locals := frame.locals.insert (tickFeeSideName above false)
    (.int (Int.ofNat (tickFeeSide a evm.accountMap evm.executionEnv above false).toNat))
  let locals := locals.insert (tickFeeSideName above true)
    (.int (Int.ofNat (tickFeeSide a evm.accountMap evm.executionEnv above true).toNat))
  {frame with locals := locals}

theorem evalTickFeeSideExpr (locals imms : Store) (evm : EVM.State) (a : TickFeeArgs)
    (above direct second : Bool)
    (hglobal : locals.get? (tickFeeGlobalName second) =
      some (.int (Int.ofNat (a.global second).toNat)))
    (halias : locals.get? (tickFeeAliasName above) = some (tickAlias (a.boundary above)))
    (hd : decide (a.direct above) = direct) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (tickFeeSideExpr above direct second) =
      .ok (.int (Int.ofNat (tickFeeSide a evm.accountMap evm.executionEnv above second).toNat)) := by
  have ho := evalTickAliasFeeGrowth locals imms evm (tickFeeAliasName above)
    (a.boundary above) second halias
  have hg := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hglobal
  cases direct
  · have hn : ¬ a.direct above := of_decide_eq_false hd
    simpa only [tickFeeSideExpr, Bool.false_eq_true, if_false, tickFeeSide, if_neg hn] using
      evalExpr_word_sub hg ho
  · have hy : a.direct above := of_decide_eq_true hd
    simpa only [tickFeeSideExpr, ↓reduceIte, tickFeeSide, if_pos hy] using ho

theorem tickFeeSideBodySource (locals imms : Store) (evm : EVM.State) (a : TickFeeArgs)
    (above direct : Bool)
    (hglobal : ∀ second, locals.get? (tickFeeGlobalName second) =
      some (.int (Int.ofNat (a.global second).toNat)))
    (halias : locals.get? (tickFeeAliasName above) = some (tickAlias (a.boundary above)))
    (hzero : ∀ second, locals.get? (tickFeeSideName above second) = some (.int 0))
    (hd : decide (a.direct above) = direct) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      (tickFeeSideBody above direct)
      (.ok (tickFeeSideFrame {contract := contract, locals := locals, immutables := imms}
        a evm above) evm) := by
  let firstLocals := locals.insert (tickFeeSideName above false)
    (.int (Int.ofNat (tickFeeSide a evm.accountMap evm.executionEnv above false).toNat))
  let first : Frame := {contract := contract, locals := firstLocals, immutables := imms}
  refine ExecBlock.consNormal (solm' := first) (evm' := evm)
    (ExecStmt.assign (evalTickFeeSideExpr locals imms evm a above direct false
      (hglobal false) halias hd) (assignLocalVarBase_frame (hzero false))) ?_
  refine ExecBlock.consNormal (solm' := tickFeeSideFrame
    {contract := contract, locals := locals, immutables := imms} a evm above) (evm' := evm)
    (ExecStmt.assign
      (value := .int (Int.ofNat (tickFeeSide a evm.accountMap evm.executionEnv above true).toNat))
      ?_ ?_) ExecBlock.nil
  · apply evalTickFeeSideExpr first.locals imms evm a above direct true
    · cases above <;> simpa only [first, firstLocals, tickFeeSideName, tickFeeGlobalName, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert, Bool.false_eq_true, if_false, if_true] using hglobal true
    · cases above <;> simpa only [first, firstLocals, tickFeeSideName, tickFeeAliasName, ↓reduceIte,
        Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using halias
    · exact hd
  · apply assignLocalVarBase_frame (old := .int 0)
    cases above <;> simpa only [first, firstLocals, tickFeeSideName, ↓reduceIte,
      Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hzero true

theorem tickFeeSideSource (locals imms : Store) (evm : EVM.State) (a : TickFeeArgs)
    (above : Bool)
    (hglobal : ∀ second, locals.get? (tickFeeGlobalName second) =
      some (.int (Int.ofNat (a.global second).toNat)))
    (halias : locals.get? (tickFeeAliasName above) = some (tickAlias (a.boundary above)))
    (hzero : ∀ second, locals.get? (tickFeeSideName above second) = some (.int 0))
    (hcurrent : locals.get? "tickCurrent" = some (.int a.current))
    (hboundary : locals.get? (if above then "tickUpper" else "tickLower") =
      some (.int (a.boundary above))) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (tickFeeSideStmt above)
      (.ok (tickFeeSideFrame {contract := contract, locals := locals, immutables := imms}
        a evm above) evm) := by
  have hc := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hcurrent
  have hb := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := {contract := contract, locals := locals, immutables := imms}) hboundary
  have he : evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (tickFeeSideCondition above) = .ok (.bool (decide (a.direct above))) := by
    cases above <;> simp only [tickFeeSideCondition, Bool.false_eq_true, if_false, if_true] at hb ⊢
    all_goals simp only [evalExpr?, hc, hb, bind, EvalResult.bind, evalBinaryOp?,
      TickFeeArgs.direct, TickFeeArgs.boundary, Bool.false_eq_true, if_false, if_true, pure]
  by_cases hd : a.direct above
  · apply ExecStmt.iteTrue (by simpa only [hd, decide_true] using he)
    exact tickFeeSideBodySource locals imms evm a above true hglobal halias hzero
      (decide_eq_true hd)
  · apply ExecStmt.iteFalse (by simpa only [hd, decide_false] using he)
    exact tickFeeSideBodySource locals imms evm a above false hglobal halias hzero
      (decide_eq_false hd)

end Benchmarks.UniswapV3.Pool
