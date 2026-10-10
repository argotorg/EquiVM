import Benchmarks.UniswapV3.Pool.SwapMemoryModel
import Benchmarks.UniswapV3.Pool.OracleWriteInternal
import Benchmarks.UniswapV3.Pool.SnapshotInside

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def swapWriteBody : List Stmt :=
  match swapTransition.body[14]! with
  | .ite _ yes _ => yes
  | _ => []

def swapWriteArgs (c : SwapCacheData) (initial : EVM.State) : OracleWriteArgs :=
  {index := slot0FieldWord 23 2 initial.accountMap initial.executionEnv
   time := c.blockTimestamp
   tick := slot0TickValue initial.accountMap initial.executionEnv
   liquidity := c.liquidityStart
   cardinality := slot0FieldWord 25 2 initial.accountMap initial.executionEnv
   cardinalityNext := slot0FieldWord 27 2 initial.accountMap initial.executionEnv}

def swapWriteCallArgs : List Expr :=
  [.field (.var "slot0Start") "observationIndex", .field (.var "cache") "blockTimestamp",
    .field (.var "slot0Start") "tick", .field (.var "cache") "liquidityStart",
    .field (.var "slot0Start") "observationCardinality",
    .field (.var "slot0Start") "observationCardinalityNext"]

theorem swapWriteCallStmt : swapWriteBody[0]! =
    .internalCall "Oracle_write" swapWriteCallArgs "__c16" := rfl

theorem evalSwapWriteGuard {frame : Frame} {evm : EVM.State}
    (s : SwapStateData) (initial : EVM.State)
    (hs : frame.locals.get? "state" = some s.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv)) :
    evalExpr? config frame evm
      (.binary .ne (.field (.var "state") "tick") (.field (.var "slot0Start") "tick")) =
      .ok (.bool (decide (s.tick ≠ slot0TickValue initial.accountMap initial.executionEnv))) :=
  evalExpr_int_ne
    (evalExpr_structField (name := "tick") (evalExpr_var_get hs) rfl)
    (evalExpr_structField (name := "tick") (evalExpr_var_get hslot) rfl)

theorem evalSwapWriteArgs {frame : Frame} {evm : EVM.State}
    (c : SwapCacheData) (initial : EVM.State)
    (hc : frame.locals.get? "cache" = some c.value)
    (hslot : frame.locals.get? "slot0Start" =
      some (slot0StructValue initial.accountMap initial.executionEnv)) :
    let a := swapWriteArgs c initial
    evalExprs? config frame evm swapWriteCallArgs =
      .ok [.int (Int.ofNat a.index.toNat), .int (Int.ofNat a.time.toNat), .int a.tick,
        .int (Int.ofNat a.liquidity.toNat), .int (Int.ofNat a.cardinality.toNat),
        .int (Int.ofNat a.cardinalityNext.toNat)] := by
  dsimp only [swapWriteArgs]
  have ec := evalExpr_var_get (cfg := config) (evm := evm) hc
  have es := evalExpr_var_get (cfg := config) (evm := evm) hslot
  have ei := evalExpr_structField (name := "observationIndex") es rfl
  have et := evalExpr_structField (name := "blockTimestamp") ec rfl
  have ek := evalExpr_structField (name := "tick") es rfl
  have el := evalExpr_structField (name := "liquidityStart") ec rfl
  have ecard := evalExpr_structField (name := "observationCardinality") es rfl
  have enext := evalExpr_structField (name := "observationCardinalityNext") es rfl
  simp only [swapWriteCallArgs, evalExprs?, ei, et, ek, el, ecard, enext,
    bind, EvalResult.bind, pure]

theorem swapWriteArgs_fits (c : SwapCacheData) (initial : EVM.State) (hc : c.Fits) :
    (swapWriteArgs c initial).Fits := by
  dsimp only [OracleWriteArgs.Fits, swapWriteArgs]
  refine ⟨?_, hc.2.2.1, ?_, hc.2.1, ?_, ?_⟩
  · exact u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by decide)
  · exact slot0TickValue_bounds initial.accountMap initial.executionEnv
  · exact u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by decide)
  · exact u256LandMaskToNatLtOfToNat (bits := 16) _ _ (by decide)

end Benchmarks.UniswapV3.Pool
