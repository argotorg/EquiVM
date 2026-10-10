import Benchmarks.UniswapV3.Pool.OracleWriteModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

macro "oracle_write_get" : tactic =>
  `(tactic| (simp only [oracleWriteTransformedFrame, oracleWriteIndexFrame, oracleWriteCardinalityFrame,
    oracleWriteLastFrame, oracleWriteZeroFrame, oracleWriteFrame, oracleWriteLocals,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl))

theorem oracleWriteZeroSource (imms : Store) (evm : EVM.State) (a : OracleWriteArgs) :
    ExecBlock config (oracleWriteFrame imms a) evm (oracleWriteFunction.body.take 2)
      (.ok (oracleWriteZeroFrame imms a) evm) := by
  let f : Frame := {oracleWriteFrame imms a with
    locals := (oracleWriteLocals a).insert "indexUpdated" (.int 0)}
  refine ExecBlock.consNormal (solm' := f) (evm' := evm)
    (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem oracleWriteLastSource (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) :
    ExecBlock config (oracleWriteFrame imms a) evm (oracleWriteFunction.body.take 3)
      (.ok (oracleWriteLastFrame imms a evm) evm) := by
  change ExecBlock config (oracleWriteFrame imms a) evm
    (oracleWriteFunction.body.take 2 ++ [oracleWriteFunction.body[2]!]) _
  exact execBlock_append_ok (oracleWriteZeroSource imms evm a)
    (ExecBlock.consNormal (ExecStmt.letDecl
      (evalOracleObservation (oracleWriteZeroFrame imms a).locals imms evm "index" a.index
        (by oracle_write_get) (by oracle_write_get) hin)) ExecBlock.nil)

theorem oracleWriteReadReverts (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : ¬ a.index.toNat < 65535) :
    ExecFuncBody config (oracleWriteFrame imms a) evm oracleWriteFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 oracleWriteFunction.body]
  exact execBlock_append_ok (oracleWriteZeroSource imms evm a)
    (ExecBlock.consRevert (ExecStmt.letDeclRevert
      (evalOracleObservationRevert (oracleWriteZeroFrame imms a).locals imms evm "index" a.index
        (by oracle_write_get) (by oracle_write_get) hin)))

theorem evalOracleWriteSame (imms : Store) (evm : EVM.State) (a : OracleWriteArgs) :
    evalExpr? config (oracleWriteLastFrame imms a evm) evm
      (.binary .eq (.field (.var "last") "blockTimestamp") (.var "blockTimestamp")) =
      .ok (.bool (oracleWriteSame a evm)) :=
  evalExpr_word_eq (evalOracleTimestamp (oracleWriteLast a evm) (by oracle_write_get))
    (evalExpr_var_get (by oracle_write_get))

theorem oracleWriteSameReturns (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) (hsame : oracleWriteSame a evm = true) :
    ExecFuncBody config (oracleWriteFrame imms a) evm oracleWriteFunction.body
      (.returned (oracleWriteLastFrame imms a evm) evm
        (some [.int (Int.ofNat a.index.toNat), .int (Int.ofNat a.cardinality.toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 3 oracleWriteFunction.body]
  apply execBlock_append_ok (oracleWriteLastSource imms evm a hin)
  apply ExecBlock.consReturn
  apply ExecStmt.iteTrue (by simpa only [hsame] using evalOracleWriteSame imms evm a)
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have hi := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteLastFrame imms a evm)
    (name := "index") (value := .int (Int.ofNat a.index.toNat)) (by oracle_write_get)
  have hc := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteLastFrame imms a evm)
    (name := "cardinality") (value := .int (Int.ofNat a.cardinality.toNat)) (by oracle_write_get)
  simp only [evalExprs?, hi, hc, bind, EvalResult.bind, pure]

theorem oracleWriteNewTimeSource (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) (hsame : oracleWriteSame a evm = false) :
    ExecBlock config (oracleWriteFrame imms a) evm (oracleWriteFunction.body.take 4)
      (.ok (oracleWriteLastFrame imms a evm) evm) := by
  change ExecBlock config (oracleWriteFrame imms a) evm
    (oracleWriteFunction.body.take 3 ++ [oracleWriteFunction.body[3]!]) _
  exact execBlock_append_ok (oracleWriteLastSource imms evm a hin)
    (ExecBlock.consNormal (ExecStmt.iteFalse
      (by simpa only [hsame] using evalOracleWriteSame imms evm a) ExecBlock.nil) ExecBlock.nil)

end Benchmarks.UniswapV3.Pool
