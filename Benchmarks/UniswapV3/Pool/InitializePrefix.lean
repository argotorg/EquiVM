import Benchmarks.UniswapV3.Pool.TickLogSource
import Benchmarks.UniswapV3.Pool.BlockTimestamp
import Benchmarks.UniswapV3.Pool.Slot0Storage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def initializeLocals (price : UInt256) : Store := tickLogLocals price

def initializeFrame (v : UniswapV3PoolImmutables) (price : UInt256) : Frame :=
  {contract := contract, locals := initializeLocals price, immutables := immStore v}

theorem initializeBind (price : UInt256) :
    bindParams? initializeTransition.params [.int (Int.ofNat price.toNat)] =
      some (initializeLocals price) := rfl

def initializeTickFrame (v : UniswapV3PoolImmutables) (price : UInt256) (tick : Int) : Frame :=
  {initializeFrame v price with locals := (initializeLocals price).insert "tick" (.int tick)}

def initializeTimeFrame (v : UniswapV3PoolImmutables) (price : UInt256)
    (tick : Int) (I : ExecutionEnv) : Frame :=
  {initializeTickFrame v price tick with
    locals := (initializeTickFrame v price tick).locals.insert "__c1"
      (.int (Int.ofNat (blockTimestampWord I).toNat))}

theorem evalInitializeUninitialized (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) :
    evalExpr? config (initializeFrame v price) evm
      (.binary .eq (.storage ⟨"slot0", [.field "sqrtPriceX96"]⟩) (.intLit 0)) =
      .ok (.bool (decide (slot0FieldWord 0 20 evm.accountMap evm.executionEnv = ⟨0⟩))) := by
  exact evalExpr_word_eq (evalSlot0SqrtPriceX96 _ _ _
    (by simp [initializeLocals, tickLogLocals])) (b := ⟨0⟩)
    (by simp only [evalExpr?, pure]; rfl)

theorem initializeGuardSource (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : slot0FieldWord 0 20 evm.accountMap evm.executionEnv = ⟨0⟩) :
    ExecBlock config (initializeFrame v price) evm (initializeTransition.body.take 2)
      (.ok (initializeFrame v price) evm) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  exact ExecBlock.consNormal (ExecStmt.requireTrue
    (by simpa only [hzero, decide_true] using evalInitializeUninitialized v evm price)) ExecBlock.nil

theorem initializeRevertsAlreadyInitialized (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : slot0FieldWord 0 20 evm.accountMap evm.executionEnv ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (initializeLocals price)
      initializeTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).requireRevert
  simpa only [hzero, decide_false] using evalInitializeUninitialized v evm price

theorem evalInitializeTickArgs (v : UniswapV3PoolImmutables) (evm : EVM.State) (price : UInt256) :
    evalExprs? config (initializeFrame v price) evm [.var "sqrtPriceX96"] =
      .ok [.int (Int.ofNat price.toNat)] := by
  have he : evalExpr? config (initializeFrame v price) evm (.var "sqrtPriceX96") =
      .ok (.int (Int.ofNat price.toNat)) := evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem initializeTickCall (v : UniswapV3PoolImmutables) (evm : EVM.State) (price : UInt256)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) (hs : tickLogSafe (tickLogResult price)) :
    ExecStmt config (initializeFrame v price) evm
      (.internalCall "TickMath_getTickAtSqrtRatio" [.var "sqrtPriceX96"] "tick")
      (.ok (initializeTickFrame v price (tickLogChoice (tickLogResult price) price)) evm) := by
  obtain ⟨out, hbody⟩ := tickLogReturns (immStore v) evm price hp hv hs
  exact internalCallFunctionReturn (callee := tickLogFunction) (calleeSolm := out)
    (evalInitializeTickArgs v evm price) tickLogLookup (tickLogBind price) hbody

theorem initializeRevertsTick (v : UniswapV3PoolImmutables) (evm : EVM.State) (price : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : slot0FieldWord 0 20 evm.accountMap evm.executionEnv = ⟨0⟩)
    (hp : price.toNat < 2 ^ 160)
    (hv : ¬ (tickLogValid price ∧ tickLogSafe (tickLogResult price))) :
    ExecTransitionBody config contract evm (initializeLocals price)
      initializeTransition.body .reverted (immStore v) := by
  have hbody : ExecFuncBody config (tickLogFrame (immStore v) price) evm tickLogFunction.body
      .reverted := by
    by_cases hvalid : tickLogValid price
    · exact tickLogCalleeReverts _ evm price hp hvalid (fun hs ↦ hv ⟨hvalid, hs⟩)
    · exact tickLogReverts _ evm price hvalid
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 initializeTransition.body]
  apply execBlock_append_ok (initializeGuardSource v evm price hwv hzero)
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := tickLogFunction)
    (evalInitializeTickArgs v evm price) tickLogLookup (tickLogBind price) hbody)

theorem initializeTimestampCall (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (tick : Int) :
    ExecStmt config (initializeTickFrame v price tick) evm
      (.internalCall "_blockTimestamp" [] "__c1")
      (.ok (initializeTimeFrame v price tick evm.executionEnv) evm) :=
  internalCallFunctionReturn (callee := blockTimestampFunction) (argVals := []) (locals := ∅)
    (calleeSolm := {contract := contract, locals := ∅, immutables := immStore v})
    (value := some [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)])
    (by simp only [evalExprs?, pure]) blockTimestampLookup rfl (blockTimestampReturns (immStore v) evm)

theorem initializeBeforeOracleSource (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (price : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hzero : slot0FieldWord 0 20 evm.accountMap evm.executionEnv = ⟨0⟩)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) (hs : tickLogSafe (tickLogResult price)) :
    ExecBlock config (initializeFrame v price) evm (initializeTransition.body.take 4)
      (.ok (initializeTimeFrame v price (tickLogChoice (tickLogResult price) price)
        evm.executionEnv) evm) := by
  change ExecBlock _ _ _ (initializeTransition.body.take 2 ++
    (initializeTransition.body.drop 2).take 2) _
  exact execBlock_append_ok (initializeGuardSource v evm price hwv hzero)
    (ExecBlock.consNormal (initializeTickCall v evm price hp hv hs)
      (ExecBlock.consNormal (initializeTimestampCall v evm price _) ExecBlock.nil))

end Benchmarks.UniswapV3.Pool
