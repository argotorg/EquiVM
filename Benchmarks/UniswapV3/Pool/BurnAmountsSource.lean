import Benchmarks.UniswapV3.Pool.BurnModel
import Benchmarks.UniswapV3.Pool.PositionOwedStorage
import Benchmarks.UniswapV3.Pool.SourceWordArithmetic
import Benchmarks.UniswapV3.Pool.LiquidityDeltaModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def burnAmount (i : Int) : UInt256 := UInt256.sub ⟨0⟩ (EVM.wordOfInt i)

def burnResultFrame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) : Frame :=
  resumeAfterInternalCall (burnCastFrame v a) "__c1"
    (some [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key), .int a0, .int a1])

def burnPositionFrame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) : Frame :=
  let frame := burnResultFrame v a key a0 a1
  {frame with locals := frame.locals.insert "position" (positionAlias key)}

def burnAmount0IntFrame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) : Frame :=
  let frame := burnPositionFrame v a key a0 a1
  {frame with locals := frame.locals.insert "amount0Int" (.int a0)}

def burnIntsFrame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) : Frame :=
  let frame := burnAmount0IntFrame v a key a0 a1
  {frame with locals := frame.locals.insert "amount1Int" (.int a1)}

def burnAmount0Frame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) : Frame :=
  let frame := burnIntsFrame v a key a0 a1
  {frame with locals := frame.locals.insert "amount0" (.int (Int.ofNat (burnAmount a0).toNat))}

def burnAmountsFrame (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) : Frame :=
  let frame := burnAmount0Frame v a key a0 a1
  {frame with locals := frame.locals.insert "amount1" (.int (Int.ofNat (burnAmount a1).toNat))}

macro "burn_amounts_get" : tactic =>
  `(tactic| (simp only [burnAmountsFrame, burnAmount0Frame, burnIntsFrame, burnAmount0IntFrame,
    burnPositionFrame, burnResultFrame, burnCastFrame, burnInitFrame, burnFrame, burnLocals,
    resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty]; rfl))

theorem burnAmount_cast (i : Int) :
    normalizeInt (.uint ⟨256, by decide⟩)
      (normalizeInt (.sint ⟨256, by decide⟩) (0 - i)) =
      Int.ofNat (burnAmount i).toNat := by
  rw [normalizeUInt_sint, normalizeUInt256_int, wordOfInt_sub]
  rfl

theorem burnLetPosition (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) :
    ExecStmt config (burnResultFrame v a key a0 a1) evm
      (.letStorage "position" ⟨"positions", [.mindex (.tupleGet (.var "__c1") 0)]⟩)
      (.ok (burnPositionFrame v a key a0 a1) evm) := by
  have hget : (burnResultFrame v a key a0 a1).locals.get? "__c1" =
      some (.tuple [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key), .int a0, .int a1]) := by
    burn_amounts_get
  have hlen : (EVM.Word.toBytesBE key).length = 32 := by
    simpa using word_toBytesBE_toByteArray_size key
  apply ExecStmt.letStorage
  apply resolveStorageRef?_ok
  · burn_amounts_get
  · simp only [evalStorageRef, evalStorageRefSteps, evalStorageRefStep, evalExpr?, hget,
      positionReference, valueToKey?, tupleGetValue?, hlen, bind, EvalResult.bind,
      EvalResult.ofOption, pure, List.getElem?_cons_zero]
    rfl
  · rfl

theorem burnAmountsSource (v : UniswapV3PoolImmutables) (a : BurnArgs)
    (key : UInt256) (a0 a1 : Int) (evm : EVM.State) :
    ExecBlock config (burnResultFrame v a key a0 a1) evm (burnTransition.body.drop 7 |>.take 5)
      (.ok (burnAmountsFrame v a key a0 a1) evm) := by
  refine ExecBlock.consNormal (burnLetPosition v a key a0 a1 evm) ?_
  have h0 : evalExpr? config (burnPositionFrame v a key a0 a1) evm
      (.tupleGet (.var "__c1") 1) = .ok (.int a0) := by
    have hg : (burnPositionFrame v a key a0 a1).locals.get? "__c1" =
        some (.tuple [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key), .int a0, .int a1]) := by
      burn_amounts_get
    simp only [evalExpr?, hg, tupleGetValue?, EvalResult.ofOption, bind, EvalResult.bind, pure,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "amount0Int") (value := .int a0) h0) ?_
  have h1 : evalExpr? config (burnAmount0IntFrame v a key a0 a1) evm
      (.tupleGet (.var "__c1") 2) = .ok (.int a1) := by
    have hg : (burnAmount0IntFrame v a key a0 a1).locals.get? "__c1" =
        some (.tuple [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE key), .int a0, .int a1]) := by
      burn_amounts_get
    simp only [evalExpr?, hg, tupleGetValue?, EvalResult.ofOption, bind, EvalResult.bind, pure,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "amount1Int") (value := .int a1) h1) ?_
  have h0i : evalExpr? config (burnIntsFrame v a key a0 a1) evm (.var "amount0Int") =
      .ok (.int a0) := evalExpr_var_get (by burn_amounts_get)
  refine ExecBlock.consNormal (solm := burnIntsFrame v a key a0 a1)
    (ExecStmt.assign (value := .int (Int.ofNat (burnAmount a0).toNat))
    (by simp only [evalExpr?, h0i, castValue?, evalBinaryOp?, bind, EvalResult.bind,
          EvalResult.ofOption, pure, burnAmount_cast])
    (assignLocalVarBase_frame (old := .int 0) (by burn_amounts_get))) ?_
  have h1i : evalExpr? config (burnAmount0Frame v a key a0 a1) evm (.var "amount1Int") =
      .ok (.int a1) := evalExpr_var_get (by burn_amounts_get)
  exact ExecBlock.consNormal (solm := burnAmount0Frame v a key a0 a1)
    (ExecStmt.assign (value := .int (Int.ofNat (burnAmount a1).toNat))
    (by simp only [evalExpr?, h1i, castValue?, evalBinaryOp?, bind, EvalResult.bind,
          EvalResult.ofOption, pure, burnAmount_cast])
    (assignLocalVarBase_frame (old := .int 0) (by burn_amounts_get))) ExecBlock.nil

end Benchmarks.UniswapV3.Pool
