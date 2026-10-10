import Benchmarks.UniswapV3.Pool.OracleWritePrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem evalOracleWriteGrows (imms : Store) (evm : EVM.State) (a : OracleWriteArgs) :
    evalExpr? config (oracleWriteLastFrame imms a evm) evm
      (.binary .and (.binary .gt (.var "cardinalityNext") (.var "cardinality"))
        (.binary .eq (.var "index") (.cast (.binary .sub (.var "cardinality") (.intLit 1))
          (.elem (.int (.uint ⟨16, by decide⟩)))))) = .ok (.bool (oracleWriteGrows a)) := by
  have hc := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteLastFrame imms a evm)
    (name := "cardinality") (value := .int (Int.ofNat a.cardinality.toNat)) (by oracle_write_get)
  have hn := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteLastFrame imms a evm)
    (name := "cardinalityNext") (value := .int (Int.ofNat a.cardinalityNext.toNat)) (by oracle_write_get)
  have hi := evalExpr_var_get (cfg := config) (evm := evm) (frame := oracleWriteLastFrame imms a evm)
    (name := "index") (value := .int (Int.ofNat a.index.toNat)) (by oracle_write_get)
  have hp : evalExpr? config (oracleWriteLastFrame imms a evm) evm
      (.cast (.binary .sub (.var "cardinality") (.intLit 1)) (.elem (.int (.uint ⟨16, by decide⟩)))) =
      .ok (.int (Int.ofNat (oracleWriteCardinalityPred a).toNat)) := by
    simp only [evalExpr?, hc, bind, EvalResult.bind, evalBinaryOp?, castValue?, EvalResult.ofOption]
    rw [normalizeUIntInt_mask ⟨16, by decide⟩ _ (UInt256.ofNat 65535) (by decide),
      wordOfInt_sub, wordOfInt_ofNat_toNat]
    rfl
  exact evalExpr_bool_and (evalExpr_word_gt hn hc) (evalExpr_word_eq hi hp)

theorem oracleWriteCardinalityChoice (imms : Store) (evm : EVM.State) (a : OracleWriteArgs) :
    ExecStmt config (oracleWriteLastFrame imms a evm) evm (oracleWriteFunction.body[4]!)
      (.ok (oracleWriteCardinalityFrame imms a evm) evm) := by
  have hc := evalOracleWriteGrows imms evm a
  cases hg : oracleWriteGrows a
  · simp only [oracleWriteCardinalityFrame, oracleWriteCardinality, hg, Bool.false_eq_true, if_false]
    apply ExecStmt.iteFalse (by simpa only [hg] using hc)
    exact ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_var_get (by oracle_write_get))
        (assignLocalVarBase_frame (old := .int 0) (by oracle_write_get))) ExecBlock.nil
  · simp only [oracleWriteCardinalityFrame, oracleWriteCardinality, hg, if_true]
    apply ExecStmt.iteTrue (by simpa only [hg] using hc)
    exact ExecBlock.consNormal
      (ExecStmt.assign (evalExpr_var_get (by oracle_write_get))
        (assignLocalVarBase_frame (old := .int 0) (by oracle_write_get))) ExecBlock.nil

theorem oracleWriteCardinalitySource (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) (hsame : oracleWriteSame a evm = false) :
    ExecBlock config (oracleWriteFrame imms a) evm (oracleWriteFunction.body.take 5)
      (.ok (oracleWriteCardinalityFrame imms a evm) evm) := by
  change ExecBlock config (oracleWriteFrame imms a) evm
    (oracleWriteFunction.body.take 4 ++ [oracleWriteFunction.body[4]!]) _
  exact execBlock_append_ok (oracleWriteNewTimeSource imms evm a hin hsame)
    (ExecBlock.consNormal (oracleWriteCardinalityChoice imms evm a) ExecBlock.nil)

theorem evalOracleWriteIndex (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hn : (oracleWriteCardinality a).toNat ≠ 0) :
    evalExpr? config (oracleWriteCardinalityFrame imms a evm) evm
      (.binary .mod (.cast (.binary .add (.var "index") (.intLit 1))
        (.elem (.int (.uint ⟨16, by decide⟩)))) (.var "cardinalityUpdated")) =
      .ok (.int (Int.ofNat (oracleWriteIndex a).toNat)) :=
  evalExpr_word_mod
    (evalOracleSearchNextIndex (frame := oracleWriteCardinalityFrame imms a evm) a.index
      (by oracle_write_get)) (evalExpr_var_get (by oracle_write_get)) hn

theorem oracleWriteIndexSource (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) (hsame : oracleWriteSame a evm = false)
    (hn : (oracleWriteCardinality a).toNat ≠ 0) :
    ExecBlock config (oracleWriteFrame imms a) evm (oracleWriteFunction.body.take 6)
      (.ok (oracleWriteIndexFrame imms a evm) evm) := by
  change ExecBlock config (oracleWriteFrame imms a) evm
    (oracleWriteFunction.body.take 5 ++ [oracleWriteFunction.body[5]!]) _
  exact execBlock_append_ok (oracleWriteCardinalitySource imms evm a hin hsame)
    (ExecBlock.consNormal (ExecStmt.assign (evalOracleWriteIndex imms evm a hn)
      (assignLocalVarBase_frame (old := .int 0) (by oracle_write_get))) ExecBlock.nil)

theorem oracleWriteCardinalityReverts (imms : Store) (evm : EVM.State) (a : OracleWriteArgs)
    (hin : a.index.toNat < 65535) (hsame : oracleWriteSame a evm = false)
    (hz : (oracleWriteCardinality a).toNat = 0) :
    ExecFuncBody config (oracleWriteFrame imms a) evm oracleWriteFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 5 oracleWriteFunction.body]
  apply execBlock_append_ok (oracleWriteCardinalitySource imms evm a hin hsame)
  apply ExecBlock.consRevert
  have hc : evalExpr? config (oracleWriteCardinalityFrame imms a evm) evm
      (.var "cardinalityUpdated") = .ok (.int 0) := by
    have he := evalExpr_var_get (cfg := config) (evm := evm)
      (frame := oracleWriteCardinalityFrame imms a evm) (name := "cardinalityUpdated")
      (value := .int (Int.ofNat (oracleWriteCardinality a).toNat)) (by oracle_write_get)
    simpa only [hz] using he
  exact ExecStmt.assignExprRevert (evalExpr_int_mod_zero
    (evalOracleSearchNextIndex a.index (by oracle_write_get)) hc)

end Benchmarks.UniswapV3.Pool
