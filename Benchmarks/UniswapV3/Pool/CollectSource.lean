import Benchmarks.UniswapV3.Pool.PositionGetSource
import Benchmarks.UniswapV3.Pool.PositionOwedStorage
import Benchmarks.UniswapV3.Pool.PoolTokenTransfer
import Benchmarks.UniswapV3.Pool.Slot0Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def collectLocals (recipient : AccountAddress) (lower upper req0 req1 : UInt256) : Store :=
  (((((∅ : Store).insert "recipient" (.address recipient)).insert "tickLower"
    (.int (positionTick lower))).insert "tickUpper" (.int (positionTick upper))).insert
    "amount0Requested" (.int (Int.ofNat req0.toNat))).insert "amount1Requested" (.int (Int.ofNat req1.toNat))

def collectFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (lower upper req0 req1 : UInt256) : Frame :=
  { contract := contract, locals := collectLocals recipient lower upper req0 req1, immutables := immStore v }

def collectInitFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (lower upper req0 req1 : UInt256) : Frame :=
  { (collectFrame v recipient lower upper req0 req1) with
    locals := ((collectLocals recipient lower upper req0 req1).insert "amount0" (.int 0)).insert
      "amount1" (.int 0) }

theorem collectInitBlock (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config (collectFrame v recipient lower upper req0 req1) evm
      (collectTransition.body.take 3) (.ok (collectInitFrame v recipient lower upper req0 req1) evm) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "amount0")
    (ty := some (.elem (.int (.uint ⟨128, by decide⟩)))) (value := .int 0)
    (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (name := "amount1")
    (ty := some (.elem (.int (.uint ⟨128, by decide⟩)))) (value := .int 0)
    (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem evalCollectUnlocked (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) :
    evalExpr? config (collectInitFrame v recipient lower upper req0 req1) evm
      (.storage ⟨"slot0", [.field "unlocked"]⟩) =
      .ok (.bool (!decide (slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  rw [← wordToElemBool]
  exact evalSlot0Unlocked _ _ _ (by simp [collectLocals])

theorem collectAssignLock (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) :
    ExecStmt config (collectInitFrame v recipient lower upper req0 req1) evm
      (.assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false))
      (.ok (collectInitFrame v recipient lower upper req0 req1) (storeSlot0Unlocked evm false)) := by
  exact ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked evm _ _ false (by simp [collectLocals]))

theorem collectLockPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config (collectFrame v recipient lower upper req0 req1) evm
      (collectTransition.body.take 5)
      (.ok (collectInitFrame v recipient lower upper req0 req1) (storeSlot0Unlocked evm false)) := by
  change ExecBlock config _ _ (collectTransition.body.take 3 ++
    [.require (.storage ⟨"slot0", [.field "unlocked"]⟩),
     .assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false)]) _
  apply execBlock_append_ok (collectInitBlock v evm recipient lower upper req0 req1 hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using
      evalCollectUnlocked v evm recipient lower upper req0 req1
  · exact ExecBlock.consNormal (collectAssignLock v evm recipient lower upper req0 req1) ExecBlock.nil

theorem collectRevertsLocked (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (collectLocals recipient lower upper req0 req1)
      collectTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 collectTransition.body]
  apply execBlock_append_ok (collectInitBlock v evm recipient lower upper req0 req1 hwv)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hlocked, decide_true, Bool.not_true] using
    evalCollectUnlocked v evm recipient lower upper req0 req1

theorem collectStatic (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (collectLocals recipient lower upper req0 req1)
      collectTransition.body .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 3 collectTransition.body]
  apply execBlock_append_ok (collectInitBlock v evm recipient lower upper req0 req1 hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using
      evalCollectUnlocked v evm recipient lower upper req0 req1
  · exact ExecBlock.consStatic (execStmt_assign_static
      (collectAssignLock v evm recipient lower upper req0 req1) hperm)

def collectKeyFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (lower upper req0 req1 key : UInt256) : Frame :=
  { (collectInitFrame v recipient lower upper req0 req1) with
    locals := (collectInitFrame v recipient lower upper req0 req1).locals.insert "__c0"
      (.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key)) }

def collectPositionFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (lower upper req0 req1 key : UInt256) : Frame :=
  { (collectKeyFrame v recipient lower upper req0 req1 key) with
    locals := (collectKeyFrame v recipient lower upper req0 req1 key).locals.insert "position" (positionAlias key) }

theorem collectCallPosition (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256) :
    ExecStmt config (collectInitFrame v recipient lower upper req0 req1) evm
      (.internalCall "Position_get" [.env .caller, .var "tickLower", .var "tickUpper"] "__c0")
      (.ok (collectKeyFrame v recipient lower upper req0 req1 (positionKey evm.executionEnv.source lower upper)) evm) := by
  have hl : evalExpr? config (collectInitFrame v recipient lower upper req0 req1) evm
      (.var "tickLower") = .ok (.int (positionTick lower)) := evalExpr_var_get (by
    simp [collectInitFrame, collectLocals, Std.HashMap.getElem_insert])
  have hu : evalExpr? config (collectInitFrame v recipient lower upper req0 req1) evm
      (.var "tickUpper") = .ok (.int (positionTick upper)) := evalExpr_var_get (by
    simp [collectInitFrame, collectLocals, Std.HashMap.getElem_insert])
  exact internalCallFunctionReturn (callee := positionGetFunction)
    (argVals := [.address evm.executionEnv.source, .int (positionTick lower), .int (positionTick upper)])
    (locals := positionGetLocals evm.executionEnv.source lower upper)
    (value := some [.fixedBytes ⟨31, by decide⟩
      (EVM.Word.toBytesBE (positionKey evm.executionEnv.source lower upper))])
    (calleeSolm := positionGetFrame (immStore v) evm.executionEnv.source lower upper)
    (by simp only [evalExprs?, evalExpr?, hl, hu, envValue, bind, EvalResult.bind, pure])
    positionGetLookup rfl (positionGetReturns (immStore v) evm evm.executionEnv.source lower upper)

theorem collectLetPosition (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 key : UInt256) :
    ExecStmt config (collectKeyFrame v recipient lower upper req0 req1 key) evm
      (.letStorage "position" ⟨"positions", [.mindex (.var "__c0")]⟩)
      (.ok (collectPositionFrame v recipient lower upper req0 req1 key) evm) := by
  apply ExecStmt.letStorage
  apply resolveStorageRef?_ok
  · simp [collectInitFrame, collectKeyFrame, collectLocals]
  · have hlen : (EVM.Word.toBytesBE key).length = 32 := by
      simpa using word_toBytesBE_toByteArray_size key
    simp [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      collectKeyFrame, positionReference, valueToKey?, hlen, bind, EvalResult.bind, EvalResult.ofOption, pure]
  · rfl

theorem collectPositionPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config (collectFrame v recipient lower upper req0 req1) evm (collectTransition.body.take 7)
      (.ok (collectPositionFrame v recipient lower upper req0 req1
        (positionKey evm.executionEnv.source lower upper)) (storeSlot0Unlocked evm false)) := by
  change ExecBlock _ _ _ (collectTransition.body.take 5 ++
    [.internalCall "Position_get" [.env .caller, .var "tickLower", .var "tickUpper"] "__c0",
     .letStorage "position" ⟨"positions", [.mindex (.var "__c0")]⟩]) _
  apply execBlock_append_ok (collectLockPrefix v evm recipient lower upper req0 req1 hwv hunlocked)
  have hc := collectCallPosition v (storeSlot0Unlocked evm false) recipient lower upper req0 req1
  rw [storeSlot0Unlocked_executionEnv] at hc
  exact ExecBlock.consNormal hc
    (ExecBlock.consNormal (collectLetPosition v _ recipient lower upper req0 req1 _) ExecBlock.nil)

def collectMinExpr (second : Bool) : Expr :=
  .ite (.binary .gt (.var (poolRequestedName second))
      (.storage ⟨"position", [.field (positionOwedField second)]⟩))
    (.storage ⟨"position", [.field (positionOwedField second)]⟩) (.var (poolRequestedName second))

theorem evalCollectMin (locals imms : Store) (evm : EVM.State)
    (key : UInt256) (second : Bool) (requested : UInt256)
    (hget : locals.get? (poolRequestedName second) = some (.int (Int.ofNat requested.toNat)))
    (hposition : locals.get? "position" = some (positionAlias key)) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm (collectMinExpr second) =
      .ok (.int (Int.ofNat (minWord requested (positionOwedWord key second evm.accountMap evm.executionEnv)).toNat)) :=
  evalExpr_minWord (evalExpr_var_get hget) (evalPositionOwed locals imms evm key second hposition)

theorem collectAssignMin (locals imms : Store) (evm : EVM.State)
    (key : UInt256) (second : Bool) (requested : UInt256) (old : Value)
    (hget : locals.get? (poolRequestedName second) = some (.int (Int.ofNat requested.toNat)))
    (hposition : locals.get? "position" = some (positionAlias key))
    (hold : locals.get? (poolAmountName second) = some old) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (.assign .localVar ⟨poolAmountName second, []⟩ (collectMinExpr second))
      (.ok { contract := contract
             locals := locals.insert (poolAmountName second) (.int (Int.ofNat
               (minWord requested (positionOwedWord key second evm.accountMap evm.executionEnv)).toNat))
             immutables := imms } evm) :=
  ExecStmt.assign (evalCollectMin locals imms evm key second requested hget hposition)
    (assignLocalVarBase_frame hold)

def collectAmountsFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (lower upper req0 req1 key amount0 amount1 : UInt256) : Frame :=
  { (collectPositionFrame v recipient lower upper req0 req1 key) with
    locals := ((collectPositionFrame v recipient lower upper req0 req1 key).locals.insert
      "amount0" (.int (Int.ofNat amount0.toNat))).insert "amount1" (.int (Int.ofNat amount1.toNat)) }

theorem collectAmounts (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (lower upper req0 req1 key : UInt256) :
    ExecBlock config (collectPositionFrame v recipient lower upper req0 req1 key) evm
      ((collectTransition.body.drop 7).take 2)
      (.ok (collectAmountsFrame v recipient lower upper req0 req1 key
        (minWord req0 (positionOwedWord key false evm.accountMap evm.executionEnv))
        (minWord req1 (positionOwedWord key true evm.accountMap evm.executionEnv))) evm) := by
  refine ExecBlock.consNormal (collectAssignMin _ _ evm key false req0 (.int 0) ?_ ?_ ?_) ?_
  · simp [poolRequestedName, collectKeyFrame, collectInitFrame,
      collectLocals, Std.HashMap.getElem_insert]
  · simp
  · simp [poolAmountName, collectKeyFrame, collectInitFrame,
      collectLocals, Std.HashMap.getElem_insert]
  refine ExecBlock.consNormal (collectAssignMin _ _ evm key true req1 (.int 0) ?_ ?_ ?_) ?_
  · simp [poolRequestedName, poolAmountName, collectKeyFrame,
      collectInitFrame, collectLocals, Std.HashMap.getElem_insert]
  · simp [poolAmountName, Std.HashMap.getElem_insert]
  · simp [poolAmountName, collectKeyFrame,
      collectInitFrame, collectLocals, Std.HashMap.getElem_insert]
  exact ExecBlock.nil

end Benchmarks.UniswapV3.Pool
