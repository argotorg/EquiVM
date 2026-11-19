import Benchmarks.Midnight.AdminSource
import Benchmarks.Midnight.MappingMemory

/-! Shared source proofs for enabling an LLTV or a liquidation cursor. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def enableArg (cursor : Bool) : Ident := if cursor then "liquidationCursor" else "lltv"
def enableName (cursor : Bool) : Ident :=
  if cursor then "isLiquidationCursorEnabled" else "isLltvEnabled"
def enableEvent (cursor : Bool) : Ident := if cursor then "EnableLiquidationCursor" else "EnableLltv"
def enableSlot (cursor : Bool) : UInt256 := if cursor then ⟨8⟩ else ⟨7⟩
def enableBound (cursor : Bool) (key : UInt256) : Prop :=
  if cursor then key.toNat < 1000000000000000000 else key.toNat ≤ 1000000000000000000
instance (cursor : Bool) (key : UInt256) : Decidable (enableBound cursor key) :=
  inferInstanceAs (Decidable (if cursor then _ else _))

def enableBoundExpr (cursor : Bool) : Expr :=
  .binary (if cursor then .lt else .le) (.var (enableArg cursor)) (.intLit 1000000000000000000)

def enableArguments (cursor : Bool) (key : UInt256) : Store :=
  (∅ : Store).insert (enableArg cursor) (.int key.toNat)

def enableBody (cursor : Bool) : List Stmt :=
  entryPrefix ++ [.require adminGuard, .require (enableBoundExpr cursor),
    .assign .storage { base := enableName cursor, steps := [.mindex (.var (enableArg cursor))] }
      (.boolLit true), .emit (enableEvent cursor) [.var (enableArg cursor)]]

def enableState (evm : EVM.State) (cursor : Bool) (key : UInt256) : EVM.State :=
  let slot := solcMappingSlot (enableSlot cursor) key
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (UInt256.lor (UInt256.land (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
      (UInt256.lnot ⟨255⟩)) ⟨1⟩)

theorem enableArgumentGet (evm : EVM.State) (cursor : Bool) (key : UInt256) :
    (calldataFrame contract (enableArguments cursor key) ∅ evm).locals.get? (enableArg cursor) =
      some (.int key.toNat) := by
  change ((enableArguments cursor key).insert "__calldata" (.bytes evm.executionEnv.calldata)).get?
    (enableArg cursor) = _
  rw [store_get_ne _ _ (by cases cursor <;> decide)]
  exact store_get_self _ _ _

theorem evalEnableBound (evm : EVM.State) (cursor : Bool) (key : UInt256) :
    evalExpr? config (calldataFrame contract (enableArguments cursor key) ∅ evm) evm
      (enableBoundExpr cursor) = .ok (.bool (decide (enableBound cursor key))) := by
  have hg := enableArgumentGet evm cursor key
  cases cursor <;>
    simp only [enableBoundExpr, Bool.false_eq_true, if_false, if_true, evalExpr?, hg,
      EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp?, enableBound]
  all_goals norm_cast

theorem assignEnable (evm : EVM.State) (cursor : Bool) (key : UInt256) :
    assignStorageRef? config (calldataFrame contract (enableArguments cursor key) ∅ evm) evm
      .storage { base := enableName cursor, steps := [.mindex (.var (enableArg cursor))] }
      (.bool true) =
      .ok (calldataFrame contract (enableArguments cursor key) ∅ evm, enableState evm cursor key) := by
  apply assignStorageRef_storage_scalar_value
    (er := { base := enableName cursor, steps := [.mindex (.int key.toNat)] })
    (ty := .elem .bool) (loc := boolOffset0Loc (solcMappingSlot (enableSlot cursor) key))
    (layout := midnightStorageLayout)
  · cases cursor <;> simp [calldataFrame, enableArguments, enableArg, enableName]
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?,
      enableArgumentGet, EvalResult.bind, EvalResult.ofOption, valueToKey?, pure, bind]
  · cases cursor <;> rfl
  · rfl
  · cases cursor <;>
      change some (StorageAddr.leaf (boolOffset0Loc (solcMappingSlot _
        (keyValueToWord (.int (Int.ofNat key.toNat)))))) = _ <;> rw [keyValueToWord_uint256] <;> rfl
  · exact Or.inl ⟨_, rfl⟩
  · exact storageLocStore_bool_true_offset0 evm _

theorem enableAuthEval (evm : EVM.State) (cursor : Bool) (key : UInt256) :
    evalExpr? config (calldataFrame contract (enableArguments cursor key) ∅ evm) evm adminGuard =
      .ok (.bool (decide (adminAllowed evm))) := by
  apply evalAdminGuard evm rfl
  cases cursor <;> simp [calldataFrame, enableArguments, enableArg]

theorem enableAuthReverts (evm : EVM.State) (cursor : Bool) (key : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : ¬ adminAllowed evm) :
    ExecTransitionBody config contract evm (enableArguments cursor key) (enableBody cursor)
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  rw [enableAuthEval, decide_eq_false hauth]

theorem enableBoundReverts (evm : EVM.State) (cursor : Bool) (key : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : adminAllowed evm)
    (hbound : ¬ enableBound cursor key) :
    ExecTransitionBody config contract evm (enableArguments cursor key) (enableBody cursor)
      .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [enableAuthEval, decide_eq_true hauth]
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  rw [evalEnableBound, decide_eq_false hbound]

theorem enableReturns (evm : EVM.State) (cursor : Bool) (key : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : adminAllowed evm)
    (hbound : enableBound cursor key) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody config contract evm (enableArguments cursor key) (enableBody cursor)
      (.returned (calldataFrame contract (enableArguments cursor key) ∅ evm)
        (enableState evm cursor key) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [enableAuthEval, decide_eq_true hauth]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [evalEnableBound, decide_eq_true hbound]
  apply ExecBlock.consNormal (ExecStmt.assign (Or.inr hperm)
    (by simp only [evalExpr?, pure]) (assignEnable evm cursor key))
  apply ExecBlock.consNormal (ExecStmt.emit (vals := [.int key.toNat]) ?_ ?_) ExecBlock.nil
  · simpa only [enableState, storageStore_executionEnv] using hperm
  · apply evalExprs?_singleton
    simp only [evalExpr?, enableArgumentGet, EvalResult.ofOption]

theorem enableStatic (evm : EVM.State) (cursor : Bool) (key : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < calldataLimit) (hauth : adminAllowed evm)
    (hbound : enableBound cursor key) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (enableArguments cursor key) (enableBody cursor)
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [enableAuthEval, decide_eq_true hauth]
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · rw [evalEnableBound, decide_eq_true hbound]
  apply ExecBlock.consStatic
  exact ExecStmt.assignStatic (by simp only [evalExpr?, pure]) (assignEnable evm cursor key) hperm

end Benchmarks.Midnight
