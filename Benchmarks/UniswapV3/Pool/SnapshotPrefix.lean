import Benchmarks.UniswapV3.Pool.NoDelegateCall
import Benchmarks.UniswapV3.Pool.CheckTicksSource
import Benchmarks.UniswapV3.Pool.TickReferences

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

abbrev snapshotTransition := snapshotCumulativesInsideTransition
def snapshotLocals (lower upper : Int) : Store :=
  ((∅ : Store).insert "tickLower" (.int lower)).insert "tickUpper" (.int upper)
def snapshotFrame (v : UniswapV3PoolImmutables) (lower upper : Int) : Frame :=
  {contract := contract, locals := snapshotLocals lower upper, immutables := immStore v}
def snapshotInitialFrame (v : UniswapV3PoolImmutables) (lower upper : Int) : Frame :=
  {snapshotFrame v lower upper with locals :=
    (((snapshotLocals lower upper).insert "tickCumulativeInside" (.int 0)).insert
      "secondsPerLiquidityInsideX128" (.int 0)).insert "secondsInside" (.int 0)}
def snapshotDelegateFrame (v : UniswapV3PoolImmutables) (lower upper : Int) : Frame :=
  {snapshotInitialFrame v lower upper with locals :=
    (snapshotInitialFrame v lower upper).locals.insert "__c0" .unit}
def snapshotCheckedFrame (v : UniswapV3PoolImmutables) (lower upper : Int) : Frame :=
  {snapshotDelegateFrame v lower upper with locals :=
    (snapshotDelegateFrame v lower upper).locals.insert "__c1" .unit}

theorem snapshotInitialPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config (snapshotFrame v lower upper) evm (snapshotTransition.body.take 4)
      (.ok (snapshotInitialFrame v lower upper) evm) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem snapshotDelegateCall (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hself : evm.executionEnv.codeOwner = v.original) :
    ExecStmt config (snapshotInitialFrame v lower upper) evm
      (.internalCall "checkNotDelegateCall" [] "__c0") (.ok (snapshotDelegateFrame v lower upper) evm) :=
  internalCallFunctionReturn (callee := noDelegateCallFunction) (argVals := []) (locals := ∅)
    (calleeSolm := noDelegateCallFrame v) (value := none)
    (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl (noDelegateCallReturns v evm hself)

theorem snapshotCheckTicksArgs (v : UniswapV3PoolImmutables) (evm : EVM.State) (lower upper : Int) :
    evalExprs? config (snapshotDelegateFrame v lower upper) evm [.var "tickLower", .var "tickUpper"] =
      .ok [.int lower, .int upper] := by
  simp [evalExprs?, evalExpr?, snapshotDelegateFrame, snapshotInitialFrame, snapshotFrame,
    snapshotLocals, checkTicksLocals, Std.HashMap.getElem_insert, EvalResult.ofOption,
    bind, EvalResult.bind, pure]

theorem snapshotCheckTicksCall (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hticks : validTicks lower upper) :
    ExecStmt config (snapshotDelegateFrame v lower upper) evm
      (.internalCall "checkTicks" [.var "tickLower", .var "tickUpper"] "__c1")
      (.ok (snapshotCheckedFrame v lower upper) evm) :=
  internalCallFunctionReturn (callee := checkTicksFunction) (locals := checkTicksLocals lower upper)
    (calleeSolm := checkTicksFrame (immStore v) lower upper) (value := none)
    (snapshotCheckTicksArgs v evm lower upper) checkTicksLookup
    (checkTicksBind lower upper) (checkTicksReturns (immStore v) evm lower upper hticks)

theorem snapshotCheckedPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : validTicks lower upper) :
    ExecBlock config (snapshotFrame v lower upper) evm (snapshotTransition.body.take 6)
      (.ok (snapshotCheckedFrame v lower upper) evm) := by
  change ExecBlock _ _ _ (snapshotTransition.body.take 4 ++ (snapshotTransition.body.drop 4).take 2) _
  apply execBlock_append_ok (snapshotInitialPrefix v evm lower upper hwv)
  exact ExecBlock.consNormal (snapshotDelegateCall v evm lower upper hself)
    (ExecBlock.consNormal (snapshotCheckTicksCall v evm lower upper hticks) ExecBlock.nil)

theorem snapshotRevertsDelegate (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner ≠ v.original) :
    ExecTransitionBody config contract evm (snapshotLocals lower upper) snapshotTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 snapshotTransition.body]
  apply execBlock_append_ok (snapshotInitialPrefix v evm lower upper hwv)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (callee := noDelegateCallFunction) (argVals := []) (locals := ∅)
    (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl (noDelegateCallReverts v evm hself)

theorem snapshotRevertsTicks (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) (hticks : ¬ validTicks lower upper) :
    ExecTransitionBody config contract evm (snapshotLocals lower upper) snapshotTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 snapshotTransition.body]
  apply execBlock_append_ok (snapshotInitialPrefix v evm lower upper hwv)
  refine ExecBlock.consNormal (snapshotDelegateCall v evm lower upper hself) ?_
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (snapshotCheckTicksArgs v evm lower upper) checkTicksLookup
    (checkTicksBind lower upper) (checkTicksReverts (immStore v) evm lower upper hticks)

def snapshotZerosFrame (v : UniswapV3PoolImmutables) (lower upper : Int) : Frame :=
  let locals := (snapshotCheckedFrame v lower upper).locals
  let locals := locals.insert "tickCumulativeLower" (.int 0)
  let locals := locals.insert "tickCumulativeUpper" (.int 0)
  let locals := locals.insert "secondsPerLiquidityOutsideLowerX128" (.int 0)
  let locals := locals.insert "secondsPerLiquidityOutsideUpperX128" (.int 0)
  let locals := locals.insert "secondsOutsideLower" (.int 0)
  { (snapshotCheckedFrame v lower upper) with
    locals := locals.insert "secondsOutsideUpper" (.int 0) }
def snapshotLowerAliasFrame (v : UniswapV3PoolImmutables) (lower upper : Int) : Frame :=
  {snapshotZerosFrame v lower upper with locals :=
    (snapshotZerosFrame v lower upper).locals.insert "lower" (tickAlias lower)}
def snapshotAliasesFrame (v : UniswapV3PoolImmutables) (lower upper : Int) : Frame :=
  {snapshotLowerAliasFrame v lower upper with locals :=
    (snapshotLowerAliasFrame v lower upper).locals.insert "upper" (tickAlias upper)}

theorem snapshotAliasPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (lower upper : Int) :
    ExecBlock config (snapshotCheckedFrame v lower upper) evm
      ((snapshotTransition.body.drop 6).take 8) (.ok (snapshotAliasesFrame v lower upper) evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  change ExecBlock config (snapshotZerosFrame v lower upper) evm _ _
  refine ExecBlock.consNormal (solm' := snapshotLowerAliasFrame v lower upper) (evm' := evm)
    (ExecStmt.letStorage ?_) ?_
  · exact resolveTickReference _ _ evm "tickLower" lower
      (by simp [snapshotCheckedFrame, snapshotDelegateFrame, snapshotInitialFrame,
        snapshotLocals, checkTicksLocals])
      (by simp [snapshotCheckedFrame, snapshotDelegateFrame, snapshotInitialFrame,
        snapshotLocals, checkTicksLocals, Std.HashMap.getElem_insert])
  refine ExecBlock.consNormal (solm' := snapshotAliasesFrame v lower upper) (evm' := evm)
    (ExecStmt.letStorage ?_) ExecBlock.nil
  exact resolveTickReference _ _ evm "tickUpper" upper
    (by simp [snapshotZerosFrame, snapshotCheckedFrame,
      snapshotDelegateFrame, snapshotInitialFrame,
      snapshotLocals, checkTicksLocals])
    (by simp [snapshotZerosFrame, snapshotCheckedFrame,
      snapshotDelegateFrame, snapshotInitialFrame,
      snapshotLocals, checkTicksLocals, Std.HashMap.getElem_insert])

end Benchmarks.UniswapV3.Pool
