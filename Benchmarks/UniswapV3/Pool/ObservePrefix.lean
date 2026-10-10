import Benchmarks.UniswapV3.Pool.OracleObserveResult
import Benchmarks.UniswapV3.Pool.PoolLiquidityStorage
import Benchmarks.UniswapV3.Pool.Slot0Storage
import Benchmarks.UniswapV3.Pool.NoDelegateCall
import Benchmarks.UniswapV3.Pool.BlockTimestamp

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def observeLocals (secondsAgos : List UInt256) : Store :=
  (∅ : Store).insert "secondsAgos" (.array (oracleSecondsAgoValues secondsAgos))
def observeFrame (v : UniswapV3PoolImmutables) (secondsAgos : List UInt256) : Frame :=
  {contract := contract, locals := observeLocals secondsAgos, immutables := immStore v}
def observeInitialFrame (v : UniswapV3PoolImmutables) (secondsAgos : List UInt256) : Frame :=
  { observeFrame v secondsAgos with
    locals := ((observeLocals secondsAgos).insert "tickCumulatives" (.array [])).insert
      "secondsPerLiquidityCumulativeX128s" (.array []) }
def observeDelegateFrame (v : UniswapV3PoolImmutables) (secondsAgos : List UInt256) : Frame :=
  { observeInitialFrame v secondsAgos with locals :=
    (observeInitialFrame v secondsAgos).locals.insert "__c0" .unit }
def observeReadyFrame (v : UniswapV3PoolImmutables) (secondsAgos : List UInt256) (I : ExecutionEnv) : Frame :=
  { observeDelegateFrame v secondsAgos with locals :=
    (observeDelegateFrame v secondsAgos).locals.insert "__c1" (.int (Int.ofNat (blockTimestampWord I).toNat)) }

def observeCallArgs : List Expr :=
  [.var "__c1", .var "secondsAgos", .storage ⟨"slot0", [.field "tick"]⟩,
   .storage ⟨"slot0", [.field "observationIndex"]⟩, .storage ⟨"liquidity", []⟩,
   .storage ⟨"slot0", [.field "observationCardinality"]⟩]

theorem observeInitialPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (secondsAgos : List UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩) :
    ExecBlock config (observeFrame v secondsAgos) evm (observeTransition.body.take 3)
      (.ok (observeInitialFrame v secondsAgos) evm) := by
  apply (ABlock.start.requireStep (evalCallvalueEq_true hwv)).run
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .array []) ?_)
    (ExecBlock.consNormal (ExecStmt.letDecl (value := .array []) ?_) ExecBlock.nil)
  · exact evalExpr_newIntArray (.sint ⟨56, by decide⟩) 0 (by simp only [evalExpr?, pure]; rfl)
  · exact evalExpr_newIntArray (.uint ⟨160, by decide⟩) 0 (by simp only [evalExpr?, pure]; rfl)

theorem observeDelegateCall (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (secondsAgos : List UInt256) (hself : evm.executionEnv.codeOwner = v.original) :
    ExecStmt config (observeInitialFrame v secondsAgos) evm
      (.internalCall "checkNotDelegateCall" [] "__c0") (.ok (observeDelegateFrame v secondsAgos) evm) :=
  internalCallFunctionReturn (callee := noDelegateCallFunction) (argVals := []) (locals := ∅)
    (calleeSolm := noDelegateCallFrame v) (value := none)
    (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl (noDelegateCallReturns v evm hself)

theorem observeTimestampCall (v : UniswapV3PoolImmutables) (evm : EVM.State) (secondsAgos : List UInt256) :
    ExecStmt config (observeDelegateFrame v secondsAgos) evm
      (.internalCall "_blockTimestamp" [] "__c1")
      (.ok (observeReadyFrame v secondsAgos evm.executionEnv) evm) :=
  internalCallFunctionReturn (callee := blockTimestampFunction) (argVals := []) (locals := ∅)
    (calleeSolm := {contract := contract, locals := ∅, immutables := immStore v})
    (value := some [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat)])
    (by simp only [evalExprs?, pure]) blockTimestampLookup rfl (blockTimestampReturns (immStore v) evm)

theorem observeReadyPrefix (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (secondsAgos : List UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner = v.original) :
    ExecBlock config (observeFrame v secondsAgos) evm (observeTransition.body.take 5)
      (.ok (observeReadyFrame v secondsAgos evm.executionEnv) evm) := by
  change ExecBlock _ _ _ (observeTransition.body.take 3 ++ (observeTransition.body.drop 3).take 2) _
  apply execBlock_append_ok (observeInitialPrefix v evm secondsAgos hwv)
  exact ExecBlock.consNormal (observeDelegateCall v evm secondsAgos hself)
    (ExecBlock.consNormal (observeTimestampCall v evm secondsAgos) ExecBlock.nil)

theorem observeRevertsDelegate (v : UniswapV3PoolImmutables) (evm : EVM.State)
    (secondsAgos : List UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hself : evm.executionEnv.codeOwner ≠ v.original) :
    ExecTransitionBody config contract evm (observeLocals secondsAgos) observeTransition.body .reverted (immStore v) := by
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 3 observeTransition.body]
  apply execBlock_append_ok (observeInitialPrefix v evm secondsAgos hwv)
  apply ExecBlock.consRevert
  exact internalCallFunctionRevert (callee := noDelegateCallFunction) (argVals := []) (locals := ∅)
    (by simp only [evalExprs?, pure]) noDelegateCallLookup rfl (noDelegateCallReverts v evm hself)

theorem evalObserveCallArgs (v : UniswapV3PoolImmutables) (evm : EVM.State) (secondsAgos : List UInt256) :
    evalExprs? config (observeReadyFrame v secondsAgos evm.executionEnv) evm observeCallArgs = .ok
      [.int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat), .array (oracleSecondsAgoValues secondsAgos),
       .int (slot0TickValue evm.accountMap evm.executionEnv),
       .int (Int.ofNat (slot0FieldWord 23 2 evm.accountMap evm.executionEnv).toNat),
       .int (Int.ofNat (poolLiquidityWord evm.accountMap evm.executionEnv).toNat),
       .int (Int.ofNat (slot0FieldWord 25 2 evm.accountMap evm.executionEnv).toNat)] := by
  have hslot : (observeReadyFrame v secondsAgos evm.executionEnv).locals.get? "slot0" = none := by
    simp [observeReadyFrame, observeDelegateFrame, observeInitialFrame, observeLocals]
  have hliq : (observeReadyFrame v secondsAgos evm.executionEnv).locals.get? "liquidity" = none := by
    simp [observeReadyFrame, observeDelegateFrame, observeInitialFrame, observeLocals]
  have ht := evalSlot0Tick _ (immStore v) evm hslot
  have hi := evalSlot0ObservationIndex _ (immStore v) evm hslot
  have hc := evalSlot0ObservationCardinality _ (immStore v) evm hslot
  have hl := evalLiquidity _ (immStore v) evm hliq
  have heT := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := observeReadyFrame v secondsAgos evm.executionEnv)
    (name := "__c1") (value := .int (Int.ofNat (blockTimestampWord evm.executionEnv).toNat))
    (by simp [observeReadyFrame])
  have heA := evalExpr_var_get (cfg := config) (evm := evm)
    (frame := observeReadyFrame v secondsAgos evm.executionEnv)
    (name := "secondsAgos") (value := .array (oracleSecondsAgoValues secondsAgos))
    (by simp [observeReadyFrame, observeDelegateFrame, observeInitialFrame, observeLocals,
      Std.HashMap.getElem_insert])
  change evalExpr? config (observeReadyFrame v secondsAgos evm.executionEnv) evm _ = _ at ht hi hc hl
  simp only [observeCallArgs, evalExprs?, heT, heA, ht, hi, hc, hl, poolLiquidityWord,
    bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
