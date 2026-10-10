import Benchmarks.UniswapV3.Pool.OracleSurroundingModel
import Benchmarks.UniswapV3.Pool.SourceReverts

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem oracleSurroundingIndexReverts (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity cardinality : UInt256) (hin : ¬ index.toNat < 65535) :
    ExecFuncBody config (oracleSurroundingFrame imms time target tick index liquidity cardinality)
      evm oracleSurroundingFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 oracleSurroundingFunction.body]
  apply execBlock_append_ok
    (oracleSurroundingZeroPrefix imms evm time target tick index liquidity cardinality)
  apply ExecBlock.consRevert (ExecStmt.assignExprRevert ?_)
  exact evalOracleObservationRevert _ imms evm "index" index
    (by simp [oracleSurroundingLocals])
    (by simp [oracleSurroundingLocals, Std.HashMap.getElem_insert]) hin

theorem oracleSurroundingZeroReverts (imms : Store) (evm : EVM.State) (time target : UInt256)
    (tick : Int) (index liquidity : UInt256) (hin : index.toNat < 65535)
    (ht : target.toNat < 2 ^ 32)
    (hf : oracleSurroundingFirst time target index evm.accountMap evm.executionEnv = false) :
    ExecFuncBody config (oracleSurroundingFrame imms time target tick index liquidity ⟨0⟩)
      evm oracleSurroundingFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 4 oracleSurroundingFunction.body]
  apply execBlock_append_ok
    (oracleSurroundingFirstPrefix imms evm time target tick index liquidity ⟨0⟩ hin ht)
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ExecBlock.nil) ?_
  · exact evalExpr_var_get (by simp [oracleSurroundingFirstFrame, hf])
  apply ExecBlock.consRevert (ExecStmt.assignExprRevert ?_)
  let f := oracleSurroundingFirstFrame imms evm time target tick index liquidity ⟨0⟩
  have hi := evalOracleSearchNextIndex (frame := f) (evm := evm) index (by
    simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
      oracleSurroundingZeroFrame, oracleSurroundingLocals, Std.HashMap.getElem_insert])
  have hc : evalExpr? config f evm (.var "cardinality") = .ok (.int 0) :=
    evalExpr_var_get (by simp [f, oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
      oracleSurroundingZeroFrame, oracleSurroundingLocals, Std.HashMap.getElem_insert])
  have hmod := evalExpr_int_mod_zero hi hc
  exact evalExpr_storage_ref_revert
    (by simp [oracleSurroundingFirstFrame, oracleSurroundingReadFrame,
      oracleSurroundingZeroFrame, oracleSurroundingLocals])
    (evalStorageRef_aindex_eval_revert hmod)

end Benchmarks.UniswapV3.Pool
