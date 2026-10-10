import Benchmarks.UniswapV3.Pool.OracleWriteCardinalitySource
import Benchmarks.UniswapV3.Pool.OracleObservationStore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def oracleWriteTransformArgs : List Expr :=
  [.var "last", .var "blockTimestamp", .var "tick", .var "liquidity"]

theorem evalOracleWriteTransformArgs (imms : Store) (evm : EVM.State) (a : OracleWriteArgs) :
    evalExprs? config (oracleWriteIndexFrame imms a evm) evm oracleWriteTransformArgs =
      .ok [(oracleWriteLast a evm).value, .int (Int.ofNat a.time.toNat), .int a.tick,
        .int (Int.ofNat a.liquidity.toNat)] := by
  have hl := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteIndexFrame imms a evm)
    (name := "last") (value := (oracleWriteLast a evm).value) (by oracle_write_get)
  have ht := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteIndexFrame imms a evm)
    (name := "blockTimestamp") (value := .int (Int.ofNat a.time.toNat)) (by oracle_write_get)
  have hk := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteIndexFrame imms a evm)
    (name := "tick") (value := .int a.tick) (by oracle_write_get)
  have hq := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteIndexFrame imms a evm)
    (name := "liquidity") (value := .int (Int.ofNat a.liquidity.toNat)) (by oracle_write_get)
  simp only [oracleWriteTransformArgs, evalExprs?, hl, ht, hk, hq, bind, EvalResult.bind, pure]

theorem oracleWriteTransformCall (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (htick : -(2 ^ 23 : Int) ≤ a.tick ∧ a.tick < 2 ^ 23) :
    ExecStmt config (oracleWriteIndexFrame imms a evm) evm
      (.internalCall "Oracle_transform" oracleWriteTransformArgs "__c0")
      (.ok (oracleWriteTransformedFrame imms a evm) evm) :=
  internalCallFunctionReturn (callee := oracleTransformFunction)
    (locals := oracleTransformLocals (oracleWriteLast a evm) a.time a.tick a.liquidity)
    (calleeSolm := oracleTransformDeltaFrame imms (oracleWriteLast a evm) a.time a.tick a.liquidity)
    (value := some [(oracleWriteResultObservation a evm).value])
    (evalOracleWriteTransformArgs imms evm a) oracleTransformLookup
    (oracleTransformBind _ _ _ _) (oracleTransformReturns imms evm _ _ _ _ htick)

theorem oracleWriteTransformedSource (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) (hsame : oracleWriteSame a evm = false)
    (hn : (oracleWriteCardinality a).toNat ≠ 0) (hfit : a.Fits) :
    ExecBlock config (oracleWriteFrame imms a) evm (oracleWriteFunction.body.take 7)
      (.ok (oracleWriteTransformedFrame imms a evm) evm) := by
  change ExecBlock config (oracleWriteFrame imms a) evm
    (oracleWriteFunction.body.take 6 ++ [oracleWriteFunction.body[6]!]) _
  exact execBlock_append_ok (oracleWriteIndexSource imms evm a hin hsame hn)
    (ExecBlock.consNormal (oracleWriteTransformCall imms evm a hfit.2.2.1) ExecBlock.nil)

def oracleWriteFinalState (a : OracleWriteArgs) (evm : EVM.State) : EVM.State :=
  oracleObservationState evm (oracleWriteIndex a) (oracleWriteResultObservation a evm)

theorem oracleWriteAssignSource (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hn : (oracleWriteCardinality a).toNat ≠ 0) (hfit : a.Fits) :
    ExecStmt config (oracleWriteTransformedFrame imms a evm) evm (oracleWriteFunction.body[7]!)
      (.ok (oracleWriteTransformedFrame imms a evm) (oracleWriteFinalState a evm)) :=
  ExecStmt.assign (evalExpr_var_get (by oracle_write_get))
    (assignOracleObservation (oracleWriteTransformedFrame imms a evm).locals imms evm
      (.var "indexUpdated") (oracleWriteIndex a) (oracleWriteResultObservation a evm)
      (by oracle_write_get) (evalExpr_var_get (by oracle_write_get)) (oracleWriteIndex_lt a hfit hn))

theorem oracleWriteReturns (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) (hsame : oracleWriteSame a evm = false)
    (hn : (oracleWriteCardinality a).toNat ≠ 0) (hfit : a.Fits) :
    ExecFuncBody config (oracleWriteFrame imms a) evm oracleWriteFunction.body
      (.returned (oracleWriteTransformedFrame imms a evm) (oracleWriteFinalState a evm)
        (some [.int (Int.ofNat (oracleWriteIndex a).toNat),
          .int (Int.ofNat (oracleWriteCardinality a).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 7 oracleWriteFunction.body]
  apply execBlock_append_ok (oracleWriteTransformedSource imms evm a hin hsame hn hfit)
  refine ExecBlock.consNormal (oracleWriteAssignSource imms evm a hn hfit) ?_
  apply ExecBlock.consReturn (ExecStmt.return ?_)
  have hi := evalExpr_var_get (cfg := config) (evm := oracleWriteFinalState a evm)
    (frame := oracleWriteTransformedFrame imms a evm) (name := "indexUpdated")
    (value := .int (Int.ofNat (oracleWriteIndex a).toNat)) (by oracle_write_get)
  have hc := evalExpr_var_get (cfg := config) (evm := oracleWriteFinalState a evm)
    (frame := oracleWriteTransformedFrame imms a evm) (name := "cardinalityUpdated")
    (value := .int (Int.ofNat (oracleWriteCardinality a).toNat)) (by oracle_write_get)
  simp only [evalExprs?, hi, hc, bind, EvalResult.bind, pure]

theorem oracleWriteStatic (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) (hsame : oracleWriteSame a evm = false)
    (hn : (oracleWriteCardinality a).toNat ≠ 0) (hfit : a.Fits)
    (hp : evm.executionEnv.perm = false) :
    ExecFuncBody config (oracleWriteFrame imms a) evm oracleWriteFunction.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 7 oracleWriteFunction.body]
  apply execBlock_append_ok (oracleWriteTransformedSource imms evm a hin hsame hn hfit)
  exact ExecBlock.consStatic (execStmt_assign_static (oracleWriteAssignSource imms evm a hn hfit) hp)

end Benchmarks.UniswapV3.Pool
