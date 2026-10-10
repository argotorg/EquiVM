import Benchmarks.UniswapV3.Pool.OracleInitializeStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def oracleInitializeFunction : FunctionDecl := contract.functions[8]!

theorem oracleInitializeLookup :
    lookupCallable? contract "Oracle_initialize" = some oracleInitializeFunction.toCallable := rfl

def oracleInitializeLocals (time : UInt256) : Store :=
  (∅ : Store).insert "time" (.int (Int.ofNat time.toNat))

def oracleInitializeFrame (imms : Store) (time : UInt256) : Frame :=
  {contract := contract, locals := oracleInitializeLocals time, immutables := imms}

theorem oracleInitializeBind (time : UInt256) :
    bindParams? oracleInitializeFunction.params [.int (Int.ofNat time.toNat)] =
      some (oracleInitializeLocals time) := rfl

def oracleInitializeReadyFrame (imms : Store) (time : UInt256) : Frame :=
  {oracleInitializeFrame imms time with
    locals := ((oracleInitializeLocals time).insert "cardinality" (.int 0)).insert "cardinalityNext" (.int 0)}

theorem oracleInitializeReadySource (imms : Store) (evm : EVM.State) (time : UInt256) :
    ExecBlock config (oracleInitializeFrame imms time) evm (oracleInitializeFunction.body.take 2)
      (.ok (oracleInitializeReadyFrame imms time) evm) := by
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)

theorem assignOracleInitialize (locals imms : Store) (evm : EVM.State) (time : UInt256)
    (hbase : locals.get? "observations" = none) (ht : time.toNat < 2 ^ 32) :
    assignStorageRef? config {contract := contract, locals := locals, immutables := imms} evm .storage
      ⟨"observations", [.aindex (.intLit 0)]⟩ (oracleInitializeValue time) =
      .ok ({contract := contract, locals := locals, immutables := imms}, oracleInitializeState evm time) := by
  have hbound : arrayIndexInBounds? config evm contract.storage "observations" [] (.int 0) = .ok () := by
    have h := observationArrayBounds evm ⟨0⟩
    simpa only [show (⟨0⟩ : UInt256).toNat = 0 from rfl, show (0 : Int) = Int.ofNat 0 from rfl,
      if_pos (by decide : 0 < 65535)] using h
  have hresolve : resolveStorageRef? config
      {contract := contract, locals := locals, immutables := imms} evm
      ⟨"observations", [.aindex (.intLit 0)]⟩ =
      .ok (⟨"observations", [.aindex (.int 0)]⟩, observationStorageType) :=
    resolveStorageRef?_ok hbase (evalStorageRef_aindex_ok (value := .int 0)
      (by simp only [evalExpr?, pure]) rfl hbound) rfl
  simp only [assignStorageRef?, hresolve, poolStorageBackend_eq, solidityStorageBackend,
    oracleInitializeWrite evm time ht, bind, EvalResult.bind, pure]

theorem evalOracleInitializeValue (imms : Store) (evm : EVM.State) (time : UInt256) :
    evalExpr? config (oracleInitializeReadyFrame imms time) evm
      (.structLit "Observation" [("blockTimestamp", .var "time"),
        ("tickCumulative", .intLit 0), ("secondsPerLiquidityCumulativeX128", .intLit 0),
        ("initialized", .boolLit true)]) = .ok (oracleInitializeValue time) := by
  have he : evalExpr? config (oracleInitializeReadyFrame imms time) evm (.var "time") =
      .ok (.int (Int.ofNat time.toNat)) := evalExpr_var_get (by
    simp only [oracleInitializeReadyFrame, oracleInitializeLocals, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert]
    rfl)
  simp only [evalExpr?, evalStructFields?, he, oracleInitializeValue,
    bind, EvalResult.bind, pure]

theorem oracleInitializeAssign (imms : Store) (evm : EVM.State) (time : UInt256)
    (ht : time.toNat < 2 ^ 32) :
    assignStorageRef? config (oracleInitializeReadyFrame imms time) evm .storage
      ⟨"observations", [.aindex (.intLit 0)]⟩ (oracleInitializeValue time) =
      .ok (oracleInitializeReadyFrame imms time, oracleInitializeState evm time) := by
  apply assignOracleInitialize _ imms evm time _ ht
  simp only [oracleInitializeReadyFrame, oracleInitializeLocals, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  rfl

theorem oracleInitializeReturns (imms : Store) (evm : EVM.State) (time : UInt256)
    (ht : time.toNat < 2 ^ 32) :
    ExecFuncBody config (oracleInitializeFrame imms time) evm oracleInitializeFunction.body
      (.returned (oracleInitializeReadyFrame imms time) (oracleInitializeState evm time)
        (some [.int 1, .int 1])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 2 oracleInitializeFunction.body]
  apply execBlock_append_ok (oracleInitializeReadySource imms evm time)
  exact ExecBlock.consNormal (ExecStmt.assign (evalOracleInitializeValue imms evm time)
    (oracleInitializeAssign imms evm time ht))
    (ExecBlock.consReturn (ExecStmt.return (by
      simp only [evalExprs?, evalExpr?, bind, EvalResult.bind, pure])))

theorem oracleInitializeStatic (imms : Store) (evm : EVM.State) (time : UInt256)
    (ht : time.toNat < 2 ^ 32) (hperm : evm.executionEnv.perm = false) :
    ExecFuncBody config (oracleInitializeFrame imms time) evm oracleInitializeFunction.body
      .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 2 oracleInitializeFunction.body]
  apply execBlock_append_ok (oracleInitializeReadySource imms evm time)
  exact ExecBlock.consStatic (ExecStmt.assignStatic (evalOracleInitializeValue imms evm time)
    (oracleInitializeAssign imms evm time ht) hperm)

end Benchmarks.UniswapV3.Pool
