import Benchmarks.UniswapV3.Pool.InitializePrefix
import Benchmarks.UniswapV3.Pool.OracleInitializeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def initializeOracleFrame (v : UniswapV3PoolImmutables) (price : UInt256)
    (tick : Int) (I : ExecutionEnv) : Frame :=
  {initializeTimeFrame v price tick I with
    locals := (initializeTimeFrame v price tick I).locals.insert "__c2" (.tuple [.int 1, .int 1])}

def initializeReadyFrame (v : UniswapV3PoolImmutables) (price : UInt256)
    (tick : Int) (I : ExecutionEnv) : Frame :=
  {initializeOracleFrame v price tick I with
    locals := ((initializeOracleFrame v price tick I).locals.insert "cardinality" (.int 1)).insert
      "cardinalityNext" (.int 1)}

theorem evalInitializeOracleArgs (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (tick : Int) :
    evalExprs? config (initializeTimeFrame v price tick evm.executionEnv) evm [.var "__c1"] =
      .ok [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)] := by
  have he : evalExpr? config (initializeTimeFrame v price tick evm.executionEnv) evm (.var "__c1") =
      .ok (.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem initializeOracleCall (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (tick : Int) :
    ExecStmt config (initializeTimeFrame v price tick evm.executionEnv) evm
      (.internalCall "Oracle_initialize" [.var "__c1"] "__c2")
      (.ok (initializeOracleFrame v price tick evm.executionEnv)
        (oracleInitializeState evm (blockTimestampWord evm.executionEnv))) :=
  internalCallFunctionReturn (callee := oracleInitializeFunction)
    (locals := oracleInitializeLocals (blockTimestampWord evm.executionEnv))
    (calleeSolm := oracleInitializeReadyFrame (immStore v) (blockTimestampWord evm.executionEnv))
    (value := some [.int 1, .int 1])
    (evalInitializeOracleArgs v evm price tick) oracleInitializeLookup (oracleInitializeBind _)
    (oracleInitializeReturns (immStore v) evm _ (blockTimestampWord_lt _))

theorem initializeOracleStatic (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (tick : Int) (hperm : evm.executionEnv.perm = false) :
    ExecStmt config (initializeTimeFrame v price tick evm.executionEnv) evm
      (.internalCall "Oracle_initialize" [.var "__c1"] "__c2") .staticViolation :=
  ExecStmt.internalCallStatic (callee := oracleInitializeFunction.toCallable)
    (evalInitializeOracleArgs v evm price tick) oracleInitializeLookup (oracleInitializeBind _)
    (oracleInitializeStatic (immStore v) evm _ (blockTimestampWord_lt _) hperm)

theorem initializeReadySource (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : slot0FieldWord 0 20 evm.accountMap evm.executionEnv = ⟨0⟩)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) (hs : tickLogSafe (tickLogResult price)) :
    ExecBlock config (initializeFrame v price) evm (initializeTransition.body.take 7)
      (.ok (initializeReadyFrame v price (tickLogChoice (tickLogResult price) price) evm.executionEnv)
        (oracleInitializeState evm (blockTimestampWord evm.executionEnv))) := by
  change ExecBlock _ _ _ (initializeTransition.body.take 4 ++
    (initializeTransition.body.drop 4).take 3) _
  apply execBlock_append_ok (initializeBeforeOracleSource v evm price hwv hzero hp hv hs)
  refine ExecBlock.consNormal (initializeOracleCall v evm price _) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 1) ?_) ?_
  · simp [evalExpr?, initializeOracleFrame, EvalResult.ofOption, tupleGetValue?,
      bind, EvalResult.bind]
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int 1) ?_) ExecBlock.nil
  simp [evalExpr?, initializeOracleFrame, EvalResult.ofOption, tupleGetValue?,
    bind, EvalResult.bind, Std.HashMap.getElem_insert]

theorem initializeStatic (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : slot0FieldWord 0 20 evm.accountMap evm.executionEnv = ⟨0⟩)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) (hs : tickLogSafe (tickLogResult price))
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (initializeLocals price)
      initializeTransition.body .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  rw [← List.take_append_drop 4 initializeTransition.body]
  exact execBlock_append_ok (initializeBeforeOracleSource v evm price hwv hzero hp hv hs)
    (ExecBlock.consStatic (initializeOracleStatic v evm price _ hperm))

end Benchmarks.UniswapV3.Pool
