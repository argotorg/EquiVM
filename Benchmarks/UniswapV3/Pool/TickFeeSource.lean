import Benchmarks.UniswapV3.Pool.TickFeePrefix
import Benchmarks.UniswapV3.Pool.TickFeeSideSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def tickFeeBelowFrame (imms : Store) (a : TickFeeArgs) (evm : EVM.State) : Frame :=
  tickFeeSideFrame (tickFeeBelowZeroFrame imms a) a evm false

def tickFeeAboveZeroFrame (imms : Store) (a : TickFeeArgs) (evm : EVM.State) : Frame :=
  let locals := ((tickFeeBelowFrame imms a evm).locals.insert "feeGrowthAbove0X128" (.int 0)).insert
    "feeGrowthAbove1X128" (.int 0)
  {tickFeeBelowFrame imms a evm with locals := locals}

def tickFeeReadyFrame (imms : Store) (a : TickFeeArgs) (evm : EVM.State) : Frame :=
  tickFeeSideFrame (tickFeeAboveZeroFrame imms a evm) a evm true

def tickFeeFirstFrame (imms : Store) (a : TickFeeArgs) (evm : EVM.State) : Frame :=
  let locals := (tickFeeReadyFrame imms a evm).locals.insert "feeGrowthInside0X128"
    (.int (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv false).toNat))
  {tickFeeReadyFrame imms a evm with locals := locals}

def tickFeeFinalFrame (imms : Store) (a : TickFeeArgs) (evm : EVM.State) : Frame :=
  let locals := (tickFeeFirstFrame imms a evm).locals.insert "feeGrowthInside1X128"
    (.int (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv true).toNat))
  {tickFeeFirstFrame imms a evm with locals := locals}

local macro "tick_fee_get" : tactic => `(tactic| (
  simp only [tickFeeFinalFrame, tickFeeFirstFrame, tickFeeReadyFrame, tickFeeAboveZeroFrame,
    tickFeeBelowFrame, tickFeeBelowZeroFrame, tickFeeAliasesFrame, tickFeeLowerAliasFrame,
    tickFeeZerosFrame, tickFeeFrame, tickFeeLocals, tickFeeSideFrame,
    tickFeeGlobalName, tickFeeAliasName, tickFeeSideName,
    TickFeeArgs.global, TickFeeArgs.boundary, Bool.false_eq_true, if_false, if_true,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  rfl))

theorem tickFeeBelowSource (imms : Store) (evm : EVM.State) (a : TickFeeArgs) :
    ExecStmt config (tickFeeBelowZeroFrame imms a) evm (tickFeeSideStmt false)
      (.ok (tickFeeBelowFrame imms a evm) evm) := by
  apply tickFeeSideSource (tickFeeBelowZeroFrame imms a).locals imms evm a false
  · intro second; cases second <;> tick_fee_get
  · tick_fee_get
  · intro second; cases second <;> tick_fee_get
  · tick_fee_get
  · tick_fee_get

theorem tickFeeAboveSource (imms : Store) (evm : EVM.State) (a : TickFeeArgs) :
    ExecStmt config (tickFeeAboveZeroFrame imms a evm) evm (tickFeeSideStmt true)
      (.ok (tickFeeReadyFrame imms a evm) evm) := by
  apply tickFeeSideSource (tickFeeAboveZeroFrame imms a evm).locals imms evm a true
  · intro second; cases second <;> tick_fee_get
  · tick_fee_get
  · intro second; cases second <;> tick_fee_get
  · tick_fee_get
  · tick_fee_get

theorem tickFeeReadySource (imms : Store) (evm : EVM.State) (a : TickFeeArgs) :
    ExecBlock config (tickFeeFrame imms a) evm (tickFeeFunction.body.take 10)
      (.ok (tickFeeReadyFrame imms a evm) evm) := by
  change ExecBlock config (tickFeeFrame imms a) evm
    (tickFeeFunction.body.take 6 ++ [tickFeeSideStmt false,
      .letDecl "feeGrowthAbove0X128" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0),
      .letDecl "feeGrowthAbove1X128" (some (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 0),
      tickFeeSideStmt true]) _
  apply execBlock_append_ok (tickFeePrefix imms evm a)
  refine ExecBlock.consNormal (tickFeeBelowSource imms evm a) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  refine ExecBlock.consNormal (solm' := tickFeeAboveZeroFrame imms a evm)
    (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ?_
  exact ExecBlock.consNormal (tickFeeAboveSource imms evm a) ExecBlock.nil

def tickFeeInsideExpr (second : Bool) : Expr :=
  .cast (.binary .sub
    (.cast (.binary .sub (.var (tickFeeGlobalName second))
      (.var (tickFeeSideName false second))) (.elem (.int (.uint ⟨256, by decide⟩))))
    (.var (tickFeeSideName true second))) (.elem (.int (.uint ⟨256, by decide⟩)))

theorem evalTickFeeInside (locals imms : Store) (evm : EVM.State) (a : TickFeeArgs)
    (second : Bool)
    (hg : locals.get? (tickFeeGlobalName second) = some (.int (Int.ofNat (a.global second).toNat)))
    (hb : locals.get? (tickFeeSideName false second) =
      some (.int (Int.ofNat (tickFeeSide a evm.accountMap evm.executionEnv false second).toNat)))
    (ha : locals.get? (tickFeeSideName true second) =
      some (.int (Int.ofNat (tickFeeSide a evm.accountMap evm.executionEnv true second).toNat))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (tickFeeInsideExpr second) =
      .ok (.int (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv second).toNat)) :=
  evalExpr_word_sub (evalExpr_word_sub (evalExpr_var_get hg) (evalExpr_var_get hb))
    (evalExpr_var_get ha)

theorem tickFeeReturns (imms : Store) (evm : EVM.State) (a : TickFeeArgs) :
    ExecFuncBody config (tickFeeFrame imms a) evm tickFeeFunction.body
      (.returned (tickFeeFinalFrame imms a evm) evm
        (some [.int (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv false).toNat),
          .int (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv true).toNat)])) := by
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 10 tickFeeFunction.body]
  apply execBlock_append_ok (tickFeeReadySource imms evm a)
  refine ExecBlock.consNormal (solm' := tickFeeFirstFrame imms a evm) (evm' := evm)
    (ExecStmt.assign (value := .int
      (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv false).toNat)) ?_ ?_) ?_
  · exact evalTickFeeInside (tickFeeReadyFrame imms a evm).locals imms evm a false
      (by tick_fee_get) (by tick_fee_get) (by tick_fee_get)
  · exact assignLocalVarBase_frame (old := .int 0) (by tick_fee_get)
  · refine ExecBlock.consNormal (solm' := tickFeeFinalFrame imms a evm) (evm' := evm)
      (ExecStmt.assign (value := .int
        (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv true).toNat)) ?_ ?_) ?_
    · exact evalTickFeeInside (tickFeeFirstFrame imms a evm).locals imms evm a true
        (by tick_fee_get) (by tick_fee_get) (by tick_fee_get)
    · exact assignLocalVarBase_frame (old := .int 0) (by tick_fee_get)
    · refine ExecBlock.consReturn (ExecStmt.return ?_)
      have h0 := evalExpr_var_get (cfg := config) (evm := evm)
        (frame := tickFeeFinalFrame imms a evm) (name := "feeGrowthInside0X128")
        (value := .int (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv false).toNat))
        (by tick_fee_get)
      have h1 := evalExpr_var_get (cfg := config) (evm := evm)
        (frame := tickFeeFinalFrame imms a evm) (name := "feeGrowthInside1X128")
        (value := .int (Int.ofNat (tickFeeInside a evm.accountMap evm.executionEnv true).toNat))
        (by tick_fee_get)
      simp only [evalExprs?, h0, h1, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
