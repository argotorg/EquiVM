import Benchmarks.UniswapV3.Pool.ProtocolFeeStorage
import Benchmarks.UniswapV3.Pool.PoolTokenTransfer
import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.FactoryOwner

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def collectProtocolLocals (recipient : AccountAddress) (req0 req1 : UInt256) : Store :=
  (((∅ : Store).insert "recipient" (.address recipient)).insert "amount0Requested"
    (.int (Int.ofNat req0.toNat))).insert "amount1Requested" (.int (Int.ofNat req1.toNat))

def collectProtocolFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (req0 req1 : UInt256) : Frame :=
  { contract := contract, locals := collectProtocolLocals recipient req0 req1, immutables := immStore v }

def collectProtocolInitFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (req0 req1 : UInt256) : Frame :=
  { (collectProtocolFrame v recipient req0 req1) with
    locals := ((collectProtocolLocals recipient req0 req1).insert "amount0" (.int 0)).insert
      "amount1" (.int 0) }

theorem collectProtocolInitBlock (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config (collectProtocolFrame v recipient req0 req1) evm
      (collectProtocolTransition.body.take 3) (.ok (collectProtocolInitFrame v recipient req0 req1) evm) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)

theorem evalCollectProtocolUnlocked (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) :
    evalExpr? config (collectProtocolInitFrame v recipient req0 req1) evm
      (.storage ⟨"slot0", [.field "unlocked"]⟩) =
      .ok (.bool (!decide (slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  rw [← wordToElemBool]
  exact evalSlot0Unlocked _ _ _ (by simp [collectProtocolLocals])

theorem collectProtocolAssignLock (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) :
    ExecStmt config (collectProtocolInitFrame v recipient req0 req1) evm
      (.assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false))
      (.ok (collectProtocolInitFrame v recipient req0 req1) (storeSlot0Unlocked evm false)) := by
  exact ExecStmt.assign (by simp only [evalExpr?, pure])
    (assignSlot0Unlocked evm _ _ false (by simp [collectProtocolLocals]))

theorem collectProtocolLockPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecBlock config (collectProtocolFrame v recipient req0 req1) evm
      (collectProtocolTransition.body.take 5)
      (.ok (collectProtocolInitFrame v recipient req0 req1) (storeSlot0Unlocked evm false)) := by
  change ExecBlock config _ _ (collectProtocolTransition.body.take 3 ++
    [.require (.storage ⟨"slot0", [.field "unlocked"]⟩),
     .assign .storage ⟨"slot0", [.field "unlocked"]⟩ (.boolLit false)]) _
  apply execBlock_append_ok (collectProtocolInitBlock v evm recipient req0 req1 hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using
      evalCollectProtocolUnlocked v evm recipient req0 req1
  · exact ExecBlock.consNormal (collectProtocolAssignLock v evm recipient req0 req1) ExecBlock.nil

theorem collectProtocolRevertsLocked (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecTransitionBody config contract evm (collectProtocolLocals recipient req0 req1)
      collectProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 collectProtocolTransition.body]
  apply execBlock_append_ok (collectProtocolInitBlock v evm recipient req0 req1 hwv)
  apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
  simpa only [hlocked, decide_true, Bool.not_true] using
    evalCollectProtocolUnlocked v evm recipient req0 req1

theorem collectProtocolStatic (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (collectProtocolLocals recipient req0 req1)
      collectProtocolTransition.body .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 3 collectProtocolTransition.body]
  apply execBlock_append_ok (collectProtocolInitBlock v evm recipient req0 req1 hwv)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [hunlocked, decide_false, Bool.not_false] using
      evalCollectProtocolUnlocked v evm recipient req0 req1
  · exact ExecBlock.consStatic (execStmt_assign_static
      (collectProtocolAssignLock v evm recipient req0 req1) hperm)

def collectProtocolOwnerFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (req0 req1 : UInt256) (owner : AccountAddress) : Frame :=
  { (collectProtocolInitFrame v recipient req0 req1) with
    locals := (collectProtocolInitFrame v recipient req0 req1).locals.insert "__c0" (.address owner) }

theorem collectProtocolCallOwner (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner]))) :
    ExecStmt config (collectProtocolInitFrame v recipient req0 req1) (storeSlot0Unlocked evm false)
      (.internalCall "factoryOwner" [] "__c0")
      (.ok (collectProtocolOwnerFrame v recipient req0 req1 owner) evm') := by
  exact internalCallFunctionReturn (args := []) (argVals := []) (locals := ∅)
    (caller := collectProtocolInitFrame v recipient req0 req1) (retVar := "__c0")
    (callee := factoryOwnerFunction) (calleeSolm := calleeFrame) (value := some [.address owner])
    (by simp only [evalExprs?, pure]) factoryOwnerLookup rfl hfactory

theorem evalCollectProtocolOwner (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (owner : AccountAddress) :
    evalExpr? config (collectProtocolOwnerFrame v recipient req0 req1 owner) evm
      (.binary .eq (.env .caller) (.var "__c0")) =
      .ok (.bool (decide (evm.executionEnv.source = owner))) := by
  have hv : evalExpr? config (collectProtocolOwnerFrame v recipient req0 req1 owner) evm
      (.var "__c0") = .ok (.address owner) :=
    evalExpr_var_get (by simp [collectProtocolOwnerFrame])
  simp [evalExpr?, hv, bind, EvalResult.bind, pure, evalBinaryOp?, envValue]
  apply Bool.eq_iff_iff.mpr
  simp

theorem collectProtocolFactoryReverts (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body .reverted) :
    ExecTransitionBody config contract evm (collectProtocolLocals recipient req0 req1)
      collectProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 5 collectProtocolTransition.body]
  apply execBlock_append_ok (collectProtocolLockPrefix v evm recipient req0 req1 hwv hunlocked)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (argVals := []) (locals := ∅)
    (by simp only [evalExprs?, pure]) factoryOwnerLookup rfl hfactory

theorem collectProtocolRevertsOwner (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner])))
    (howner : evm'.executionEnv.source ≠ owner) :
    ExecTransitionBody config contract evm (collectProtocolLocals recipient req0 req1)
      collectProtocolTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 5 collectProtocolTransition.body]
  apply execBlock_append_ok (collectProtocolLockPrefix v evm recipient req0 req1 hwv hunlocked)
  apply ExecBlock.consNormal (collectProtocolCallOwner v evm evm' recipient req0 req1 owner calleeFrame hfactory)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [howner, decide_false] using evalCollectProtocolOwner v evm' recipient req0 req1 owner

theorem collectProtocolOwnerPrefix (v : UniswapV3PoolImmutables) (evm evm' : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (owner : AccountAddress) (calleeFrame : Frame)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : slot0FieldWord 30 1 evm.accountMap evm.executionEnv ≠ ⟨0⟩)
    (hfactory : ExecFuncBody config
      { contract := contract, locals := ∅, immutables := immStore v }
      (storeSlot0Unlocked evm false) factoryOwnerFunction.body
      (.returned calleeFrame evm' (some [.address owner])))
    (howner : evm'.executionEnv.source = owner) :
    ExecBlock config (collectProtocolFrame v recipient req0 req1) evm (collectProtocolTransition.body.take 7)
      (.ok (collectProtocolOwnerFrame v recipient req0 req1 owner) evm') := by
  change ExecBlock _ _ _ (collectProtocolTransition.body.take 5 ++
    [.internalCall "factoryOwner" [] "__c0",
     .require (.binary .eq (.env .caller) (.var "__c0"))]) _
  apply execBlock_append_ok (collectProtocolLockPrefix v evm recipient req0 req1 hwv hunlocked)
  apply ExecBlock.consNormal (collectProtocolCallOwner v evm evm' recipient req0 req1 owner calleeFrame hfactory)
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil
  simpa only [howner, decide_true] using evalCollectProtocolOwner v evm' recipient req0 req1 owner

def collectProtocolMinExpr (second : Bool) : Expr :=
  .ite (.binary .gt (.var (poolRequestedName second)) (protocolFeesExpr second))
    (protocolFeesExpr second) (.var (poolRequestedName second))

theorem evalCollectProtocolMin (locals imms : Store) (evm : EVM.State)
    (second : Bool) (requested : UInt256)
    (hget : locals.get? (poolRequestedName second) = some (.int (Int.ofNat requested.toNat)))
    (hbase : locals.get? "protocolFees" = none) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (collectProtocolMinExpr second) =
      .ok (.int (Int.ofNat (minWord requested
        (protocolFeesWord second evm.accountMap evm.executionEnv)).toNat)) := by
  have hr := evalExpr_var_get (cfg := config) (evm := evm) (frame :=
    {contract := contract, locals := locals, immutables := imms}) hget
  have hf := evalProtocolFeesWord locals imms evm second hbase
  exact evalExpr_minWord hr hf

theorem collectProtocolAssignMin (locals imms : Store) (evm : EVM.State)
    (second : Bool) (requested : UInt256) (old : Value)
    (hget : locals.get? (poolRequestedName second) = some (.int (Int.ofNat requested.toNat)))
    (hbase : locals.get? "protocolFees" = none)
    (hold : locals.get? (poolAmountName second) = some old) :
    ExecStmt config {contract := contract, locals := locals, immutables := imms} evm
      (.assign .localVar ⟨poolAmountName second, []⟩ (collectProtocolMinExpr second))
      (.ok {contract := contract, locals := locals.insert (poolAmountName second) (.int (Int.ofNat (minWord requested
          (protocolFeesWord second evm.accountMap evm.executionEnv)).toNat)), immutables := imms} evm) :=
  ExecStmt.assign (evalCollectProtocolMin locals imms evm second requested hget hbase)
    (assignLocalVarBase_frame hold)

def collectProtocolAmountsFrame (v : UniswapV3PoolImmutables) (recipient : AccountAddress)
    (req0 req1 : UInt256) (owner : AccountAddress) (amount0 amount1 : UInt256) : Frame :=
  { (collectProtocolOwnerFrame v recipient req0 req1 owner) with
    locals := ((collectProtocolOwnerFrame v recipient req0 req1 owner).locals.insert
      "amount0" (.int (Int.ofNat amount0.toNat))).insert "amount1" (.int (Int.ofNat amount1.toNat)) }

theorem collectProtocolAmounts (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (recipient : AccountAddress) (req0 req1 : UInt256) (owner : AccountAddress) :
    ExecBlock config (collectProtocolOwnerFrame v recipient req0 req1 owner) evm
      ((collectProtocolTransition.body.drop 7).take 2)
      (.ok (collectProtocolAmountsFrame v recipient req0 req1 owner
        (minWord req0 (protocolFeesWord false evm.accountMap evm.executionEnv))
        (minWord req1 (protocolFeesWord true evm.accountMap evm.executionEnv))) evm) := by
  refine ExecBlock.consNormal (collectProtocolAssignMin _ _ evm false req0 (.int 0) ?_ ?_ ?_) ?_
  · simp [poolRequestedName, collectProtocolInitFrame,
      collectProtocolLocals, Std.HashMap.getElem_insert]
  · simp [collectProtocolInitFrame, collectProtocolLocals]
  · simp [poolAmountName, collectProtocolInitFrame,
      collectProtocolLocals, Std.HashMap.getElem_insert]
  refine ExecBlock.consNormal (collectProtocolAssignMin _ _ evm true req1 (.int 0) ?_ ?_ ?_) ?_
  · simp [poolRequestedName, poolAmountName,
      collectProtocolInitFrame, collectProtocolLocals, Std.HashMap.getElem_insert]
  · simp [collectProtocolInitFrame, collectProtocolLocals,
      poolAmountName]
  · simp [poolAmountName, collectProtocolInitFrame,
      collectProtocolLocals, Std.HashMap.getElem_insert]
  exact ExecBlock.nil

end Benchmarks.UniswapV3.Pool
