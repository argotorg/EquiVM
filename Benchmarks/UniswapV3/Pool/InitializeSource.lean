import Benchmarks.UniswapV3.Pool.InitializeOracleSource
import Benchmarks.UniswapV3.Pool.InitializeSlot0Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem initializeReadyLookup (v : UniswapV3PoolImmutables) (price : UInt256)
    (tick : Int) (I : ExecutionEnv) :
    let locals := (initializeReadyFrame v price tick I).locals
    locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) ∧
    locals.get? "tick" = some (.int tick) ∧
    locals.get? "cardinality" = some (.int 1) ∧
    locals.get? "cardinalityNext" = some (.int 1) ∧
    locals.get? "slot0" = none := by
  simp only [initializeReadyFrame, initializeOracleFrame, initializeTimeFrame,
    initializeTickFrame, initializeLocals, tickLogLocals, Std.HashMap.get?_eq_getElem?,
    Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]
  exact ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem evalInitializeSlot0Value (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (tick : Int) (I : ExecutionEnv) :
    evalExpr? config (initializeReadyFrame v price tick I) evm
      (.structLit "Slot0" [("sqrtPriceX96", .var "sqrtPriceX96"), ("tick", .var "tick"),
        ("observationIndex", .intLit 0), ("observationCardinality", .var "cardinality"),
        ("observationCardinalityNext", .var "cardinalityNext"),
        ("feeProtocol", .intLit 0), ("unlocked", .boolLit true)]) =
      .ok (initializeSlot0Value price tick) := by
  obtain ⟨hp, ht, hc, hn, _⟩ := initializeReadyLookup v price tick I
  have h0 := evalExpr_var_get (cfg := config) (evm := evm) hp
  have h1 := evalExpr_var_get (cfg := config) (evm := evm) ht
  have h2 := evalExpr_var_get (cfg := config) (evm := evm) hc
  have h3 := evalExpr_var_get (cfg := config) (evm := evm) hn
  simp only [evalExpr?, evalStructFields?, h0, h1, h2, h3, initializeSlot0Value,
    bind, EvalResult.bind, pure]

theorem initializeReturns (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : slot0FieldWord 0 20 evm.accountMap evm.executionEnv = ⟨0⟩)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) (hs : tickLogSafe (tickLogResult price)) :
    ExecTransitionBody config contract evm (initializeLocals price) initializeTransition.body
      (.returned (initializeReadyFrame v price (tickLogChoice (tickLogResult price) price)
        evm.executionEnv)
        (initializeSlot0State (oracleInitializeState evm (blockTimestampWord evm.executionEnv))
          price (tickLogChoice (tickLogResult price) price)) none) (immStore v) := by
  apply ExecFuncBody.execBlockOK
  rw [← List.take_append_drop 7 initializeTransition.body]
  apply execBlock_append_ok (initializeReadySource v evm price hwv hzero hp hv hs)
  have hlookup := initializeReadyLookup v price (tickLogChoice (tickLogResult price) price)
    evm.executionEnv
  refine ExecBlock.consNormal (ExecStmt.assign (evalInitializeSlot0Value v _ price _ _)
    (assignInitializeSlot0 _ _ _ price _ hlookup.2.2.2.2 hp)) ?_
  refine ExecBlock.consNormal (ExecStmt.emit
    (vals := [.int (Int.ofNat price.toNat), .int (tickLogChoice (tickLogResult price) price)]) ?_)
    ExecBlock.nil
  change evalExprs? config
    (initializeReadyFrame v price (tickLogChoice (tickLogResult price) price) evm.executionEnv)
    _ [.var "sqrtPriceX96", .var "tick"] = _
  have h0 := evalExpr_var_get (cfg := config)
    (evm := initializeSlot0State (oracleInitializeState evm (blockTimestampWord evm.executionEnv))
      price (tickLogChoice (tickLogResult price) price)) hlookup.1
  have h1 := evalExpr_var_get (cfg := config)
    (evm := initializeSlot0State (oracleInitializeState evm (blockTimestampWord evm.executionEnv))
      price (tickLogChoice (tickLogResult price) price)) hlookup.2.1
  simp only [evalExprs?, h0, h1, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
