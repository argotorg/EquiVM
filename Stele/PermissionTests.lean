import Stele.Interp.Sound

variable {fork : Ethereum.Fork}

/-! Permission regressions for the relational semantics. A forbidden operation has only the
static-violation result, including failed calls and creations. Evaluation may still revert before
the operation is reached. Local assignments and zero-value calls do not require write permission. -/

namespace Stele.PermissionTests

variable {cfg : Config} {stele stele' : Frame} {evm evm' : EVM.State} {result : ExecResult}

theorem storageAssign_static_only
    (hp : evm.executionEnv.perm = false)
    (he : evalExpr? cfg stele evm expr = .ok value)
    (hs : assignStorageRef? cfg stele evm .storage ref value = .ok (stele', evm'))
    (h : ExecStmt fork cfg stele evm (.assign .storage ref expr) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem transientAssign_static_only
    (hp : evm.executionEnv.perm = false)
    (he : evalExpr? cfg stele evm expr = .ok value)
    (hs : assignStorageRef? cfg stele evm .transient ref value = .ok (stele', evm'))
    (h : ExecStmt fork cfg stele evm (.assign .transient ref expr) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem pushVal_static_only
    (hp : evm.executionEnv.perm = false)
    (he : evalExpr? cfg stele evm expr = .ok value)
    (hs : pushArray? cfg stele evm ref (some value) = .ok evm')
    (h : ExecStmt fork cfg stele evm (.push ref (some expr)) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem pushGrow_static_only
    (hp : evm.executionEnv.perm = false)
    (hs : pushArray? cfg stele evm ref none = .ok evm')
    (h : ExecStmt fork cfg stele evm (.push ref none) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem pop_static_only
    (hp : evm.executionEnv.perm = false)
    (hs : popArray? cfg stele evm ref = .ok evm')
    (h : ExecStmt fork cfg stele evm (.pop ref) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem delete_static_only
    (hp : evm.executionEnv.perm = false)
    (hs : deleteStorage? cfg stele evm ref = .ok evm')
    (h : ExecStmt fork cfg stele evm (.delete ref) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem emit_static_only
    (hp : evm.executionEnv.perm = false)
    (he : evalExprs? cfg stele evm args = .ok values)
    (h : ExecStmt fork cfg stele evm (.emit name args) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem externalCall_static_only
    (hp : evm.executionEnv.perm = false)
    (hr : evalExpr? cfg stele evm receiver = .ok (.address target))
    (hv : evalExpr? cfg stele evm eth = .ok (.int value))
    (ha : evalExprs? cfg stele evm args = .ok values)
    (hn : EVM.wordOfInt value ≠ ⟨0⟩)
    (h : ExecStmt fork cfg stele evm (.externalCall receiver name eth args retVar perm) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem lowLevelCall_static_only
    (hp : evm.executionEnv.perm = false)
    (hr : evalExpr? cfg stele evm receiver = .ok (.address target))
    (hv : evalExpr? cfg stele evm eth = .ok (.int value))
    (hd : evalExpr? cfg stele evm data = .ok (.bytes calldata))
    (hn : EVM.wordOfInt value ≠ ⟨0⟩)
    (h : ExecStmt fork cfg stele evm (.lowLevelCall receiver eth data okVar dataVar perm) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem checkedCall_static_only
    (hp : evm.executionEnv.perm = false)
    (hr : evalExpr? cfg stele evm receiver = .ok (.address target))
    (hv : evalExpr? cfg stele evm eth = .ok (.int value))
    (ha : evalExprs? cfg stele evm args = .ok values)
    (hn : EVM.wordOfInt value ≠ ⟨0⟩)
    (h : ExecStmt fork cfg stele evm
      (.checkedCall receiver name eth args retVar onSuccess errVar onFail perm) result) :
    result = .staticViolation := by
  cases h <;> simp_all

theorem new_static_only
    (hp : evm.executionEnv.perm = false)
    (hv : evalExpr? cfg stele evm eth = .ok (.int value))
    (ha : evalExprs? cfg stele evm args = .ok values)
    (h : ExecStmt fork cfg stele evm (.new name eth args retVar salt) result) :
    result = .staticViolation := by
  cases h <;> simp_all

example (he : evalExpr? cfg stele evm expr = .ok value)
    (hs : assignStorageRef? cfg stele evm .localVar ref value = .ok (stele', evm')) :
    ExecStmt fork cfg stele evm (.assign .localVar ref expr) (.ok stele' evm') :=
  .assign (Or.inl rfl) he hs

example (he : evalExpr? cfg stele evm expr = .revert) :
    ExecStmt fork cfg stele evm (.assign .storage ref expr) .reverted :=
  .assignExprRevert he

example (hr : evalExpr? cfg stele evm receiver = .ok (.address target))
    (hv : evalExpr? cfg stele evm eth = .ok (.int 0))
    (hd : evalExpr? cfg stele evm data = .ok (.bytes calldata))
    (hc : callViaEVM fork evm (EVM.address target) 0 calldata (true, evm', out) perm) :
    ExecStmt fork cfg stele evm (.lowLevelCall receiver eth data okVar dataVar perm)
      (.ok { stele with locals :=
        (stele.locals.insert okVar (.bool true)).insert dataVar (.bytes out) } evm') :=
  .lowLevelCallSuccess (Or.inl rfl) hr hv hd hc

example (hr : evalExpr? cfg stele evm receiver = .ok (.address target))
    (hv : evalExpr? cfg stele evm eth = .ok (.int 0))
    (hd : evalExpr? cfg stele evm data = .ok (.bytes calldata))
    (hc : callViaEVM fork evm (EVM.address target) 0 calldata (false, evm', out) perm) :
    ExecStmt fork cfg stele evm (.lowLevelCall receiver eth data okVar dataVar perm)
      (.ok { stele with locals :=
        (stele.locals.insert okVar (.bool false)).insert dataVar (.bytes out) } evm') :=
  .lowLevelCallFailure (Or.inl rfl) hr hv hd hc

example (hp : evm.executionEnv.perm = true)
    (he : evalExpr? cfg stele evm expr = .ok value)
    (hs : assignStorageRef? cfg stele evm .storage ref value = .ok (stele', evm')) :
    ExecStmt fork cfg stele evm (.assign .storage ref expr) (.ok stele' evm') :=
  .assign (Or.inr hp) he hs

example (hp : evm.executionEnv.perm = false)
    (he : evalExpr? cfg stele evm expr = .ok value)
    (hs : assignStorageRef? cfg stele evm .storage ref value = .ok (stele', evm')) :
    ExecBlock fork cfg stele evm (.assign .storage ref expr :: rest) .staticViolation :=
  .consStatic (.assignStatic he hs hp)

end Stele.PermissionTests
