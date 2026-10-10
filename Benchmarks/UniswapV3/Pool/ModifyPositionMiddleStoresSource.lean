import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleModel
import Benchmarks.UniswapV3.Pool.Slot0ObservationStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def modifyPositionMiddleStoresState (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : EVM.State :=
  let args := modifyPositionMiddleOracleArgs v a evm
  let updated := modifyPositionUpdatedState v a evm
  storeSlot0ObservationField
    (storeSlot0ObservationField (modifyPositionMiddleOracleState v a evm) false
      (oracleWriteResultIndex args updated)) true (oracleWriteResultCardinality args updated)

private theorem storePairSource (locals imms : Store) (state : EVM.State) (index cardinality : UInt256)
    (hbase : locals.get? "slot0" = none)
    (hget : locals.get? "__c7" = some (.tuple [.int (Int.ofNat index.toNat),
      .int (Int.ofNat cardinality.toNat)])) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} state
      ((modifyPositionMiddleBody.drop 3).take 2)
      (.ok {contract := contract, locals := locals, immutables := imms}
        (storeSlot0ObservationField (storeSlot0ObservationField state false index) true cardinality)) := by
  have heval (state' : EVM.State) (second : Bool) :
      evalExpr? config {contract := contract, locals := locals, immutables := imms} state'
        (.tupleGet (.var "__c7") (if second then 1 else 0)) =
        .ok (.int (Int.ofNat (if second then cardinality else index).toNat)) := by
    cases second <;>
      simp only [Bool.false_eq_true, if_false, if_true, evalExpr?, hget,
        EvalResult.ofOption, bind, EvalResult.bind, tupleGetValue?] <;> rfl
  exact ExecBlock.consNormal (ExecStmt.assign (heval _ false)
    (assignSlot0ObservationField _ locals imms false index hbase))
    (ExecBlock.consNormal (ExecStmt.assign (heval _ true)
      (assignSlot0ObservationField _ locals imms true cardinality hbase)) ExecBlock.nil)

theorem modifyPositionMiddleStoresSource (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) :
    ExecBlock config (modifyPositionMiddleOracleFrame v a evm) (modifyPositionMiddleOracleState v a evm)
      ((modifyPositionMiddleBody.drop 3).take 2)
      (.ok (modifyPositionMiddleOracleFrame v a evm) (modifyPositionMiddleStoresState v a evm)) := by
  have hf : modifyPositionMiddleOracleFrame v a evm =
      {contract := contract, locals := (modifyPositionMiddleOracleFrame v a evm).locals,
        immutables := immStore v} := rfl
  have hr := storePairSource (modifyPositionMiddleOracleFrame v a evm).locals (immStore v)
    (modifyPositionMiddleOracleState v a evm)
    (oracleWriteResultIndex (modifyPositionMiddleOracleArgs v a evm) (modifyPositionUpdatedState v a evm))
    (oracleWriteResultCardinality (modifyPositionMiddleOracleArgs v a evm) (modifyPositionUpdatedState v a evm))
    (by modify_position_middle_get) (by modify_position_middle_get)
  rw [← hf] at hr
  exact hr

end Benchmarks.UniswapV3.Pool
