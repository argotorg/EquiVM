import Benchmarks.UniswapV3.Pool.ModifyPositionGuards
import Benchmarks.UniswapV3.Pool.SignedAmountDeltaInternal
import Benchmarks.UniswapV3.Pool.TickSqrtInternal

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def modifyPositionOutsideArgs (a : ModifyPositionArgs) : SignedAmountDeltaArgs :=
  {sqrtA := tickSqrtValue a.lower, sqrtB := tickSqrtValue a.upper, liquidity := a.delta}

def modifyPositionOutsideLowerName (second : Bool) : Ident := if second then "__c13" else "__c3"
def modifyPositionOutsideUpperName (second : Bool) : Ident := if second then "__c14" else "__c4"
def modifyPositionOutsideAmountName (second : Bool) : Ident := if second then "__c15" else "__c5"

def modifyPositionOutsideLowerFrame (imms : Store) (a : ModifyPositionArgs)
    (evm : EVM.State) (second : Bool) : Frame :=
  resumeAfterInternalCall (modifyPositionUpdatedFrame imms a evm)
    (modifyPositionOutsideLowerName second) (some [.int (Int.ofNat (tickSqrtValue a.lower).toNat)])

def modifyPositionOutsideUpperFrame (imms : Store) (a : ModifyPositionArgs)
    (evm : EVM.State) (second : Bool) : Frame :=
  resumeAfterInternalCall (modifyPositionOutsideLowerFrame imms a evm second)
    (modifyPositionOutsideUpperName second) (some [.int (Int.ofNat (tickSqrtValue a.upper).toNat)])

noncomputable def modifyPositionOutsideAmountFrame (imms : Store) (a : ModifyPositionArgs)
    (evm : EVM.State) (second : Bool) : Frame :=
  resumeAfterInternalCall (modifyPositionOutsideUpperFrame imms a evm second)
    (modifyPositionOutsideAmountName second)
    (some [.int (signedAmountDeltaResult second (modifyPositionOutsideArgs a))])

noncomputable def modifyPositionOutsideFinalFrame (imms : Store) (a : ModifyPositionArgs)
    (evm : EVM.State) (second : Bool) : Frame :=
  let frame := modifyPositionOutsideAmountFrame imms a evm second
  let locals := frame.locals.insert (if second then "amount1" else "amount0")
    (.int (signedAmountDeltaResult second (modifyPositionOutsideArgs a)))
  {frame with locals := locals}

def modifyPositionOutsideAmountExprs (second : Bool) : List Expr :=
  [.var (modifyPositionOutsideLowerName second), .var (modifyPositionOutsideUpperName second),
    .field (.var "params") "liquidityDelta"]

def modifyPositionOutsideBody (second : Bool) : List Stmt :=
  [.internalCall "TickMath_getSqrtRatioAtTick" [.field (.var "params") "tickLower"]
      (modifyPositionOutsideLowerName second),
    .internalCall "TickMath_getSqrtRatioAtTick" [.field (.var "params") "tickUpper"]
      (modifyPositionOutsideUpperName second),
    .internalCall (signedAmountDeltaName second) (modifyPositionOutsideAmountExprs second)
      (modifyPositionOutsideAmountName second),
    .assign .localVar ⟨if second then "amount1" else "amount0", []⟩
      (.var (modifyPositionOutsideAmountName second))]

theorem modifyPositionOutsideArgs_fits (a : ModifyPositionArgs) (ha : a.Fits) :
    (modifyPositionOutsideArgs a).Fits :=
  ⟨tickSqrtValue_lt160 a.lower, tickSqrtValue_lt160 a.upper, ha.2.2⟩

theorem modifyPositionTickValid (a : ModifyPositionArgs) (ht : validTicks a.lower a.upper)
    (upper : Bool) : (if upper then a.upper else a.lower).natAbs ≤ 887272 := by
  rcases ht with ⟨ho, hl, hu⟩
  cases upper <;> simp only [Bool.false_eq_true, if_false, if_true] <;> omega

macro "modify_position_outside_get" : tactic =>
  `(tactic| (simp only [modifyPositionOutsideFinalFrame, modifyPositionOutsideAmountFrame,
    modifyPositionOutsideUpperFrame, modifyPositionOutsideLowerFrame,
    modifyPositionOutsideLowerName, modifyPositionOutsideUpperName, modifyPositionOutsideAmountName,
    Bool.false_eq_true, if_false, if_true, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; modify_position_updated_get))

theorem modifyPositionOutsideUpperFrame_eq (imms : Store) (a : ModifyPositionArgs)
    (evm : EVM.State) (second : Bool) :
    modifyPositionOutsideUpperFrame imms a evm second =
      {contract := contract, locals := (modifyPositionOutsideUpperFrame imms a evm second).locals,
        immutables := imms} := by cases second <;> rfl

theorem evalModifyPositionOutsideAmountExprs (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (second : Bool) :
    evalExprs? config (modifyPositionOutsideUpperFrame imms a evm second) evm'
      (modifyPositionOutsideAmountExprs second) = .ok
      [.int (Int.ofNat (tickSqrtValue a.lower).toNat),
        .int (Int.ofNat (tickSqrtValue a.upper).toNat), .int a.delta] := by
  have hl : evalExpr? config (modifyPositionOutsideUpperFrame imms a evm second) evm'
      (.var (modifyPositionOutsideLowerName second)) =
      .ok (.int (Int.ofNat (tickSqrtValue a.lower).toNat)) :=
    evalExpr_var_get (by cases second <;> modify_position_outside_get)
  have hu : evalExpr? config (modifyPositionOutsideUpperFrame imms a evm second) evm'
      (.var (modifyPositionOutsideUpperName second)) =
      .ok (.int (Int.ofNat (tickSqrtValue a.upper).toNat)) :=
    evalExpr_var_get (by cases second <;> modify_position_outside_get)
  have hp : evalExpr? config (modifyPositionOutsideUpperFrame imms a evm second) evm'
      (.var "params") = .ok a.value :=
    evalExpr_var_get (by cases second <;> modify_position_outside_get)
  have hd := evalExpr_structField (name := "liquidityDelta") hp rfl
  simp only [modifyPositionOutsideAmountExprs, evalExprs?, hl, hu, hd, bind, EvalResult.bind, pure]

theorem modifyPositionOutsideAssignSource (imms : Store) (a : ModifyPositionArgs)
    (evm evm' : EVM.State) (second : Bool) :
    ExecStmt config (modifyPositionOutsideAmountFrame imms a evm second) evm'
      (.assign .localVar ⟨if second then "amount1" else "amount0", []⟩
        (.var (modifyPositionOutsideAmountName second)))
      (.ok (modifyPositionOutsideFinalFrame imms a evm second) evm') := by
  exact ExecStmt.assign (evalExpr_var_get (by cases second <;> modify_position_outside_get))
    (assignLocalVarBase_frame (old := .int 0) (by cases second <;> modify_position_outside_get))

end Benchmarks.UniswapV3.Pool
