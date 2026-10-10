import Benchmarks.UniswapV3.Pool.BurnAmountsSource
import Benchmarks.UniswapV3.Pool.FlashProtocolWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def burnHasAmounts (a0 a1 : Int) : Bool :=
  decide (0 < (burnAmount a0).toNat) || decide (0 < (burnAmount a1).toNat)

def burnOwedValue (key : UInt256) (a0 a1 : Int) (evm : EVM.State) (second : Bool) : UInt256 :=
  uint128Word (positionOwedWord key second evm.accountMap evm.executionEnv +
    burnAmount (if second then a1 else a0))

def burnOwed0Frame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) : Frame :=
  let frame := burnAmountsFrame v a key a0 a1
  {frame with locals := frame.locals.insert "__t2" (.int (Int.ofNat (burnOwedValue key a0 a1 evm false).toNat))}

def burnOwedFrame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) : Frame :=
  let frame := burnOwed0Frame v a key a0 a1 evm
  {frame with locals := frame.locals.insert "__t3" (.int (Int.ofNat (burnOwedValue key a0 a1 evm true).toNat))}

def burnOwedState (key : UInt256) (a0 a1 : Int) (evm : EVM.State) : EVM.State :=
  storePositionOwed (storePositionOwed evm key false (burnOwedValue key a0 a1 evm false))
    key true (burnOwedValue key a0 a1 evm true)

def burnOwedExpr (second : Bool) : Expr :=
  .cast (.binary .add (.storage ⟨"position", [.field (positionOwedField second)]⟩)
    (.cast (.var (if second then "amount1" else "amount0")) (.elem (.int (.uint ⟨128, by decide⟩)))))
    (.elem (.int (.uint ⟨128, by decide⟩)))

def burnOwedBody : List Stmt :=
  [.letDecl "__t2" none (burnOwedExpr false), .letDecl "__t3" none (burnOwedExpr true),
    .assign .storage ⟨"position", [.field "tokensOwed0"]⟩ (.var "__t2"),
    .assign .storage ⟨"position", [.field "tokensOwed1"]⟩ (.var "__t3")]

macro "burn_owed_get" : tactic =>
  `(tactic| (simp only [burnOwedFrame, burnOwed0Frame, burnAmountsFrame, burnAmount0Frame,
    burnIntsFrame, burnAmount0IntFrame, burnPositionFrame, burnResultFrame, burnCastFrame,
    burnInitFrame, burnFrame, burnLocals, resumeAfterInternalCall,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, Std.HashMap.getElem?_empty]; rfl))

theorem evalBurnOwedExpr (locals imms : Store) (evm : EVM.State)
    (key : UInt256) (a0 a1 : Int) (second : Bool)
    (hpos : locals.get? "position" = some (positionAlias key))
    (hget : locals.get? (if second then "amount1" else "amount0") =
      some (.int (Int.ofNat (burnAmount (if second then a1 else a0)).toNat))) :
    evalExpr? config {contract := contract, locals := locals, immutables := imms} evm
      (burnOwedExpr second) = .ok (.int (Int.ofNat (burnOwedValue key a0 a1 evm second).toNat)) :=
  evalExpr_uint128AddCast (evalPositionOwed locals imms evm key second hpos)
    (evalExpr_var_get hget)

theorem burnOwedSource (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) :
    ExecBlock config (burnAmountsFrame v a key a0 a1) evm burnOwedBody
      (.ok (burnOwedFrame v a key a0 a1 evm) (burnOwedState key a0 a1 evm)) := by
  have he0 : evalExpr? config (burnAmountsFrame v a key a0 a1) evm (burnOwedExpr false) =
      .ok (.int (Int.ofNat (burnOwedValue key a0 a1 evm false).toNat)) :=
    evalBurnOwedExpr _ (immStore v) evm key a0 a1 false
      (by burn_owed_get) (by burn_owed_get)
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "__t2") he0) ?_
  have he1 : evalExpr? config (burnOwed0Frame v a key a0 a1 evm) evm (burnOwedExpr true) =
      .ok (.int (Int.ofNat (burnOwedValue key a0 a1 evm true).toNat)) :=
    evalBurnOwedExpr _ (immStore v) evm key a0 a1 true
      (by burn_owed_get) (by burn_owed_get)
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "__t3") he1) ?_
  refine ExecBlock.consNormal (solm := burnOwedFrame v a key a0 a1 evm)
    (ExecStmt.assign (value := .int (Int.ofNat (burnOwedValue key a0 a1 evm false).toNat))
      (evalExpr_var_get (by burn_owed_get))
      (assignPositionOwed _ (immStore v) evm key false _ (by burn_owed_get))) ?_
  exact ExecBlock.consNormal (solm := burnOwedFrame v a key a0 a1 evm)
    (ExecStmt.assign (value := .int (Int.ofNat (burnOwedValue key a0 a1 evm true).toNat))
      (evalExpr_var_get (by burn_owed_get))
      (assignPositionOwed _ (immStore v) _ key true _ (by burn_owed_get))) ExecBlock.nil

theorem evalBurnHasAmounts (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) :
    evalExpr? config (burnAmountsFrame v a key a0 a1) evm
      (.binary .or (.binary .gt (.var "amount0") (.intLit 0))
        (.binary .gt (.var "amount1") (.intLit 0))) = .ok (.bool (burnHasAmounts a0 a1)) := by
  have h0 : evalExpr? config (burnAmountsFrame v a key a0 a1) evm (.var "amount0") =
      .ok (.int (Int.ofNat (burnAmount a0).toNat)) := evalExpr_var_get (by burn_amounts_get)
  have h1 : evalExpr? config (burnAmountsFrame v a key a0 a1) evm (.var "amount1") =
      .ok (.int (Int.ofNat (burnAmount a1).toNat)) := evalExpr_var_get (by burn_amounts_get)
  have hz : evalExpr? config (burnAmountsFrame v a key a0 a1) evm (.intLit 0) =
      .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp only [evalExpr?, pure, show (⟨0⟩ : UInt256).toNat = 0 from by decide]
    exact congrArg (fun i : Int ↦ (EvalResult.ok (.int i) : EvalResult Value))
      (by decide : (0 : Int) = Int.ofNat 0)
  exact evalExpr_bool_or (evalExpr_word_gt (b := ⟨0⟩) h0 hz)
    (evalExpr_word_gt (b := ⟨0⟩) h1 hz)

end Benchmarks.UniswapV3.Pool
