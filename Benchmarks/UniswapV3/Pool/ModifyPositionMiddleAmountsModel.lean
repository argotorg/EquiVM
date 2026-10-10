import Benchmarks.UniswapV3.Pool.ModifyPositionMiddleStoresSource
import Benchmarks.UniswapV3.Pool.ModifyPositionOutsideModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000
attribute [local irreducible] modifyPositionUpdatedState

def modifyPositionMiddleAmountArgs (a : ModifyPositionArgs) (evm : EVM.State)
    (second : Bool) : SignedAmountDeltaArgs :=
  let sqrt := slot0FieldWord 0 20 evm.accountMap evm.executionEnv
  {sqrtA := if second then tickSqrtValue a.lower else sqrt,
    sqrtB := if second then sqrt else tickSqrtValue a.upper, liquidity := a.delta}

def modifyPositionMiddleUpperFrame (v : UniswapV3PoolImmutables) (a : ModifyPositionArgs)
    (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (modifyPositionMiddleOracleFrame v a evm) "__c8"
    (some [.int (Int.ofNat (tickSqrtValue a.upper).toNat)])

noncomputable def modifyPositionMiddleAmount0Frame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (modifyPositionMiddleUpperFrame v a evm) "__c9"
    (some [.int (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false))])

noncomputable def modifyPositionMiddleAssigned0Frame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  let frame := modifyPositionMiddleAmount0Frame v a evm
  let locals := frame.locals.insert "amount0"
    (.int (signedAmountDeltaResult false (modifyPositionMiddleAmountArgs a evm false)))
  {frame with locals := locals}

noncomputable def modifyPositionMiddleLowerFrame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (modifyPositionMiddleAssigned0Frame v a evm) "__c10"
    (some [.int (Int.ofNat (tickSqrtValue a.lower).toNat)])

noncomputable def modifyPositionMiddleAmount1Frame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  resumeAfterInternalCall (modifyPositionMiddleLowerFrame v a evm) "__c11"
    (some [.int (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true))])

noncomputable def modifyPositionMiddleAssigned1Frame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) : Frame :=
  let frame := modifyPositionMiddleAmount1Frame v a evm
  let locals := frame.locals.insert "amount1"
    (.int (signedAmountDeltaResult true (modifyPositionMiddleAmountArgs a evm true)))
  {frame with locals := locals}

noncomputable def modifyPositionMiddleBeforeSqrtFrame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) (second : Bool) : Frame :=
  if second then modifyPositionMiddleAssigned0Frame v a evm else modifyPositionMiddleOracleFrame v a evm

noncomputable def modifyPositionMiddleSqrtFrame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) (second : Bool) : Frame :=
  if second then modifyPositionMiddleLowerFrame v a evm else modifyPositionMiddleUpperFrame v a evm

noncomputable def modifyPositionMiddleAmountFrame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) (second : Bool) : Frame :=
  if second then modifyPositionMiddleAmount1Frame v a evm else modifyPositionMiddleAmount0Frame v a evm

noncomputable def modifyPositionMiddleAssignedFrame (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) (second : Bool) : Frame :=
  if second then modifyPositionMiddleAssigned1Frame v a evm else modifyPositionMiddleAssigned0Frame v a evm

def modifyPositionMiddleAmountName (second : Bool) : Ident := if second then "__c11" else "__c9"

def modifyPositionMiddleAmountExprs (second : Bool) : List Expr :=
  if second then [.var "__c10", .field (.var "_slot0") "sqrtPriceX96",
      .field (.var "params") "liquidityDelta"]
  else [.field (.var "_slot0") "sqrtPriceX96", .var "__c8",
      .field (.var "params") "liquidityDelta"]

macro "modify_position_middle_amount_get" : tactic =>
  `(tactic| (simp only [modifyPositionMiddleBeforeSqrtFrame, modifyPositionMiddleSqrtFrame,
    modifyPositionMiddleAmountFrame, modifyPositionMiddleAssignedFrame,
    modifyPositionMiddleAssigned1Frame, modifyPositionMiddleAmount1Frame,
    modifyPositionMiddleLowerFrame, modifyPositionMiddleAssigned0Frame,
    modifyPositionMiddleAmount0Frame, modifyPositionMiddleUpperFrame,
    modifyPositionMiddleAmountName, modifyPositionMiddleOracleFrame, modifyPositionMiddleTimeFrame,
    modifyPositionMiddleLiquidityFrame, modifyPositionUpdatedFrame, modifyPositionUpdateFrame,
    modifyPositionSlotFrame, modifyPositionCheckedFrame, modifyPositionDelegateFrame,
    modifyPositionZeroFrame, modifyPositionAmount0ZeroFrame, modifyPositionPositionZeroFrame,
    modifyPositionFrame, modifyPositionLocals, Bool.false_eq_true, if_false, if_true,
    resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty]; rfl))

theorem modifyPositionMiddleAmountArgs_fits (a : ModifyPositionArgs) (evm : EVM.State)
    (second : Bool) (ha : a.Fits) : (modifyPositionMiddleAmountArgs a evm second).Fits := by
  have hs : (slot0FieldWord 0 20 evm.accountMap evm.executionEnv).toNat < 2 ^ 160 :=
    u256LandMaskToNatLtOfToNat (bits := 160) _ _ (by decide)
  cases second
  · exact ⟨hs, tickSqrtValue_lt160 a.upper, ha.2.2⟩
  · exact ⟨tickSqrtValue_lt160 a.lower, hs, ha.2.2⟩

theorem modifyPositionMiddleSqrtFrame_eq (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm : EVM.State) (second : Bool) :
    modifyPositionMiddleSqrtFrame v a evm second =
      {contract := contract, locals := (modifyPositionMiddleSqrtFrame v a evm second).locals,
        immutables := immStore v} := by cases second <;> rfl

theorem evalModifyPositionMiddleAmountExprs (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm evm' : EVM.State) (second : Bool) :
    evalExprs? config (modifyPositionMiddleSqrtFrame v a evm second) evm'
      (modifyPositionMiddleAmountExprs second) = .ok
      [.int (Int.ofNat (modifyPositionMiddleAmountArgs a evm second).sqrtA.toNat),
        .int (Int.ofNat (modifyPositionMiddleAmountArgs a evm second).sqrtB.toNat), .int a.delta] := by
  have hs : evalExpr? config (modifyPositionMiddleSqrtFrame v a evm second) evm' (.var "_slot0") =
      .ok (slot0StructValue evm.accountMap evm.executionEnv) :=
    evalExpr_var_get (by cases second <;> modify_position_middle_amount_get)
  have hc := evalExpr_structField (name := "sqrtPriceX96") hs rfl
  have hp : evalExpr? config (modifyPositionMiddleSqrtFrame v a evm second) evm' (.var "params") =
      .ok a.value := evalExpr_var_get (by cases second <;> modify_position_middle_amount_get)
  have hd := evalExpr_structField (name := "liquidityDelta") hp rfl
  have ht : evalExpr? config (modifyPositionMiddleSqrtFrame v a evm second) evm'
      (.var (if second then "__c10" else "__c8")) =
      .ok (.int (Int.ofNat (tickSqrtValue (if second then a.lower else a.upper)).toNat)) :=
    evalExpr_var_get (by cases second <;> modify_position_middle_amount_get)
  cases second <;> simp only [Bool.false_eq_true, if_false, if_true] at ht
  all_goals simp only [modifyPositionMiddleAmountExprs, modifyPositionMiddleAmountArgs,
    Bool.false_eq_true, if_false, if_true, evalExprs?, hc, hd, ht, bind, EvalResult.bind, pure]

theorem modifyPositionMiddleAssignAmountSource (v : UniswapV3PoolImmutables)
    (a : ModifyPositionArgs) (evm evm' : EVM.State) (second : Bool) :
    ExecStmt config (modifyPositionMiddleAmountFrame v a evm second) evm'
      (.assign .localVar ⟨if second then "amount1" else "amount0", []⟩
        (.var (modifyPositionMiddleAmountName second)))
      (.ok (modifyPositionMiddleAssignedFrame v a evm second) evm') := by
  cases second <;>
    exact ExecStmt.assign (value := .int (signedAmountDeltaResult _ (modifyPositionMiddleAmountArgs a evm _)))
      (evalExpr_var_get (by modify_position_middle_amount_get))
      (assignLocalVarBase_frame (old := .int 0) (by modify_position_middle_amount_get))

end Benchmarks.UniswapV3.Pool
