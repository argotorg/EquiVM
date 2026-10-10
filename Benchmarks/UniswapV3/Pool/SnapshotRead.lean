import Benchmarks.UniswapV3.Pool.SnapshotPrefix
import Benchmarks.UniswapV3.Pool.Slot0Struct

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

structure TickOutside where
  cumulative : Int
  secondsPerLiquidity : UInt256
  seconds : UInt256
  initialized : Bool

def tickOutside (key : Int) (σ : AccountMap) (I : ExecutionEnv) : TickOutside :=
  ⟨tickSignedFieldValue key 3 0 ⟨56, by decide⟩ σ I,
   tickFieldWord key 3 7 20 σ I, tickFieldWord key 3 27 4 σ I,
   !decide (tickFieldWord key 3 31 1 σ I = ⟨0⟩)⟩

def snapshotLowerReadFrame (locals imms : Store) (outside : TickOutside) : Frame :=
  let l1 := locals.insert "initializedLower" (.bool false)
  let l2 := l1.insert "__t2" (.int outside.cumulative)
  let l3 := l2.insert "__t3" (.int (Int.ofNat outside.secondsPerLiquidity.toNat))
  let l4 := l3.insert "__t4" (.int (Int.ofNat outside.seconds.toNat))
  let l5 := l4.insert "__t5" (.bool outside.initialized)
  let l6 := l5.insert "tickCumulativeLower" (.int outside.cumulative)
  let l7 := l6.insert "secondsPerLiquidityOutsideLowerX128" (.int (Int.ofNat outside.secondsPerLiquidity.toNat))
  let l8 := l7.insert "secondsOutsideLower" (.int (Int.ofNat outside.seconds.toNat))
  let l9 := l8.insert "initializedLower" (.bool outside.initialized)
  {contract := contract, locals := l9, immutables := imms}

theorem snapshotLowerRead (locals imms : Store) (evm : EVM.State) (key : Int)
    (ha : locals.get? "lower" = some (tickAlias key))
    (ht : locals.get? "tickCumulativeLower" = some (.int 0))
    (hl : locals.get? "secondsPerLiquidityOutsideLowerX128" = some (.int 0))
    (hs : locals.get? "secondsOutsideLower" = some (.int 0)) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      ((snapshotTransition.body.drop 14).take 9)
      (.ok (snapshotLowerReadFrame locals imms (tickOutside key evm.accountMap evm.executionEnv)) evm) := by
  let outside := tickOutside key evm.accountMap evm.executionEnv
  simp only [Std.HashMap.get?_eq_getElem?] at ha ht hl hs
  let l1 := locals.insert "initializedLower" (.bool false)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l1, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .bool false) (by simp only [evalExpr?, pure])) ?_
  let l2 := l1.insert "__t2" (.int outside.cumulative)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l2, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .int outside.cumulative) ?_) ?_
  · simpa only [outside, tickOutside] using evalTickAliasCumulative l1 imms evm "lower" key
      (by simp [l1, Std.HashMap.getElem?_insert, ha])
  let l3 := l2.insert "__t3" (.int (Int.ofNat outside.secondsPerLiquidity.toNat))
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l3, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .int (Int.ofNat outside.secondsPerLiquidity.toNat)) ?_) ?_
  · exact evalTickAliasSecondsPerLiquidity l2 imms evm "lower" key
      (by simp [l2, l1, Std.HashMap.getElem?_insert, ha])
  let l4 := l3.insert "__t4" (.int (Int.ofNat outside.seconds.toNat))
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l4, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .int (Int.ofNat outside.seconds.toNat)) ?_) ?_
  · exact evalTickAliasSeconds l3 imms evm "lower" key
      (by simp [l3, l2, l1, Std.HashMap.getElem?_insert, ha])
  let l5 := l4.insert "__t5" (.bool outside.initialized)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l5, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .bool outside.initialized) ?_) ?_
  · simpa only [wordToElemBool] using evalTickAliasInitialized l4 imms evm "lower" key
      (by simp [l4, l3, l2, l1, Std.HashMap.getElem?_insert, ha])
  let l6 := l5.insert "tickCumulativeLower" (.int outside.cumulative)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l6, immutables := imms}) (evm' := evm)
    (ExecStmt.assign (value := .int outside.cumulative) ?_ ?_) ?_
  · exact evalExpr_var_get (by simp [l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  · exact assignLocalVarBase_frame (old := .int 0) (by simp [l5, l4, l3, l2, l1, Std.HashMap.getElem?_insert, ht])
  let l7 := l6.insert "secondsPerLiquidityOutsideLowerX128" (.int (Int.ofNat outside.secondsPerLiquidity.toNat))
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l7, immutables := imms}) (evm' := evm)
    (ExecStmt.assign (value := .int (Int.ofNat outside.secondsPerLiquidity.toNat)) ?_ ?_) ?_
  · exact evalExpr_var_get (by simp [l6, l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  · exact assignLocalVarBase_frame (old := .int 0) (by simp [l6, l5, l4, l3, l2, l1, Std.HashMap.getElem?_insert, hl])
  let l8 := l7.insert "secondsOutsideLower" (.int (Int.ofNat outside.seconds.toNat))
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l8, immutables := imms}) (evm' := evm)
    (ExecStmt.assign (value := .int (Int.ofNat outside.seconds.toNat)) ?_ ?_) ?_
  · exact evalExpr_var_get (by simp [l7, l6, l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  · exact assignLocalVarBase_frame (old := .int 0) (by simp [l7, l6, l5, l4, l3, l2, l1, Std.HashMap.getElem?_insert, hs])
  let l9 := l8.insert "initializedLower" (.bool outside.initialized)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l9, immutables := imms}) (evm' := evm)
    (ExecStmt.assign (value := .bool outside.initialized) ?_ ?_) ?_
  · exact evalExpr_var_get (by simp [l8, l7, l6, l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  · exact assignLocalVarBase_frame (old := .bool false) (by simp [l8, l7, l6, l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  exact ExecBlock.nil

def snapshotUpperReadFrame (locals imms : Store) (outside : TickOutside) : Frame :=
  let l1 := locals.insert "initializedUpper" (.bool false)
  let l2 := l1.insert "__t6" (.int outside.cumulative)
  let l3 := l2.insert "__t7" (.int (Int.ofNat outside.secondsPerLiquidity.toNat))
  let l4 := l3.insert "__t8" (.int (Int.ofNat outside.seconds.toNat))
  let l5 := l4.insert "__t9" (.bool outside.initialized)
  let l6 := l5.insert "tickCumulativeUpper" (.int outside.cumulative)
  let l7 := l6.insert "secondsPerLiquidityOutsideUpperX128" (.int (Int.ofNat outside.secondsPerLiquidity.toNat))
  let l8 := l7.insert "secondsOutsideUpper" (.int (Int.ofNat outside.seconds.toNat))
  let l9 := l8.insert "initializedUpper" (.bool outside.initialized)
  {contract := contract, locals := l9, immutables := imms}

theorem snapshotUpperRead (locals imms : Store) (evm : EVM.State) (key : Int)
    (ha : locals.get? "upper" = some (tickAlias key))
    (ht : locals.get? "tickCumulativeUpper" = some (.int 0))
    (hl : locals.get? "secondsPerLiquidityOutsideUpperX128" = some (.int 0))
    (hs : locals.get? "secondsOutsideUpper" = some (.int 0)) :
    ExecBlock config {contract := contract, locals := locals, immutables := imms} evm
      ((snapshotTransition.body.drop 24).take 9)
      (.ok (snapshotUpperReadFrame locals imms (tickOutside key evm.accountMap evm.executionEnv)) evm) := by
  let outside := tickOutside key evm.accountMap evm.executionEnv
  simp only [Std.HashMap.get?_eq_getElem?] at ha ht hl hs
  let l1 := locals.insert "initializedUpper" (.bool false)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l1, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .bool false) (by simp only [evalExpr?, pure])) ?_
  let l2 := l1.insert "__t6" (.int outside.cumulative)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l2, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .int outside.cumulative) ?_) ?_
  · simpa only [outside, tickOutside] using evalTickAliasCumulative l1 imms evm "upper" key
      (by simp [l1, Std.HashMap.getElem?_insert, ha])
  let l3 := l2.insert "__t7" (.int (Int.ofNat outside.secondsPerLiquidity.toNat))
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l3, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .int (Int.ofNat outside.secondsPerLiquidity.toNat)) ?_) ?_
  · exact evalTickAliasSecondsPerLiquidity l2 imms evm "upper" key
      (by simp [l2, l1, Std.HashMap.getElem?_insert, ha])
  let l4 := l3.insert "__t8" (.int (Int.ofNat outside.seconds.toNat))
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l4, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .int (Int.ofNat outside.seconds.toNat)) ?_) ?_
  · exact evalTickAliasSeconds l3 imms evm "upper" key
      (by simp [l3, l2, l1, Std.HashMap.getElem?_insert, ha])
  let l5 := l4.insert "__t9" (.bool outside.initialized)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l5, immutables := imms}) (evm' := evm)
    (ExecStmt.letDecl (value := .bool outside.initialized) ?_) ?_
  · simpa only [wordToElemBool] using evalTickAliasInitialized l4 imms evm "upper" key
      (by simp [l4, l3, l2, l1, Std.HashMap.getElem?_insert, ha])
  let l6 := l5.insert "tickCumulativeUpper" (.int outside.cumulative)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l6, immutables := imms}) (evm' := evm)
    (ExecStmt.assign (value := .int outside.cumulative) ?_ ?_) ?_
  · exact evalExpr_var_get (by simp [l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  · exact assignLocalVarBase_frame (old := .int 0) (by simp [l5, l4, l3, l2, l1, Std.HashMap.getElem?_insert, ht])
  let l7 := l6.insert "secondsPerLiquidityOutsideUpperX128" (.int (Int.ofNat outside.secondsPerLiquidity.toNat))
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l7, immutables := imms}) (evm' := evm)
    (ExecStmt.assign (value := .int (Int.ofNat outside.secondsPerLiquidity.toNat)) ?_ ?_) ?_
  · exact evalExpr_var_get (by simp [l6, l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  · exact assignLocalVarBase_frame (old := .int 0) (by simp [l6, l5, l4, l3, l2, l1, Std.HashMap.getElem?_insert, hl])
  let l8 := l7.insert "secondsOutsideUpper" (.int (Int.ofNat outside.seconds.toNat))
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l8, immutables := imms}) (evm' := evm)
    (ExecStmt.assign (value := .int (Int.ofNat outside.seconds.toNat)) ?_ ?_) ?_
  · exact evalExpr_var_get (by simp [l7, l6, l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  · exact assignLocalVarBase_frame (old := .int 0) (by simp [l7, l6, l5, l4, l3, l2, l1, Std.HashMap.getElem?_insert, hs])
  let l9 := l8.insert "initializedUpper" (.bool outside.initialized)
  refine ExecBlock.consNormal (solm' := {contract := contract, locals := l9, immutables := imms}) (evm' := evm)
    (ExecStmt.assign (value := .bool outside.initialized) ?_ ?_) ?_
  · exact evalExpr_var_get (by simp [l8, l7, l6, l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  · exact assignLocalVarBase_frame (old := .bool false) (by simp [l8, l7, l6, l5, l4, l3, l2, l1, Std.HashMap.getElem_insert])
  exact ExecBlock.nil

theorem evalSnapshotLowerInitialized (locals imms : Store) (evm : EVM.State)
    (outside : TickOutside) :
    evalExpr? config (snapshotLowerReadFrame locals imms outside) evm
      (.var "initializedLower") = .ok (.bool outside.initialized) :=
  evalExpr_var_get (by simp [snapshotLowerReadFrame])

theorem evalSnapshotUpperInitialized (locals imms : Store) (evm : EVM.State)
    (outside : TickOutside) :
    evalExpr? config (snapshotUpperReadFrame locals imms outside) evm
      (.var "initializedUpper") = .ok (.bool outside.initialized) :=
  evalExpr_var_get (by simp [snapshotUpperReadFrame])

end Benchmarks.UniswapV3.Pool
