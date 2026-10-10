import Benchmarks.UniswapV3.Pool.MintModel
import Benchmarks.UniswapV3.Pool.ModifyPositionUpdateSource
import Benchmarks.UniswapV3.Pool.SourceWordArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Reasoning.Immutables Benchmarks.UniswapV3.Pool.Immutables
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def mintResultFrame (v : UniswapV3PoolImmutables) (a : MintArgs)
    (a0 a1 : Int) : Frame :=
  resumeAfterInternalCall (mintCastFrame v a) "__c1"
    (some [.fixedBytes ⟨31, by decide⟩ (EVM.Word.toBytesBE (modifyPositionKey (mintModifyArgs a))),
      .int a0, .int a1])

def mintAmount0IntFrame (v : UniswapV3PoolImmutables) (a : MintArgs)
    (a0 a1 : Int) : Frame :=
  let frame := mintResultFrame v a a0 a1
  {frame with locals := frame.locals.insert "amount0Int" (.int a0)}

def mintIntsFrame (v : UniswapV3PoolImmutables) (a : MintArgs)
    (a0 a1 : Int) : Frame :=
  let frame := mintAmount0IntFrame v a a0 a1
  {frame with locals := frame.locals.insert "amount1Int" (.int a1)}

def mintAmount0Frame (v : UniswapV3PoolImmutables) (a : MintArgs)
    (a0 a1 : Int) : Frame :=
  let frame := mintIntsFrame v a a0 a1
  {frame with locals := frame.locals.insert "amount0" (.int (Int.ofNat (EVM.wordOfInt a0).toNat))}

def mintAmountsFrame (v : UniswapV3PoolImmutables) (a : MintArgs)
    (a0 a1 : Int) : Frame :=
  let frame := mintAmount0Frame v a a0 a1
  {frame with locals := frame.locals.insert "amount1" (.int (Int.ofNat (EVM.wordOfInt a1).toNat))}

macro "mint_amounts_get" : tactic =>
  `(tactic| (simp only [mintAmountsFrame, mintAmount0Frame, mintIntsFrame, mintAmount0IntFrame,
    mintResultFrame, mintCastFrame, mintInitFrame, poolAmountsFrame, mintFrame, mintLocals,
    resumeAfterInternalCall, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
    Std.HashMap.getElem?_empty]; rfl))

theorem mintAmountsSource (v : UniswapV3PoolImmutables) (a : MintArgs)
    (a0 a1 : Int) (evm : EVM.State) :
    ExecBlock config (mintResultFrame v a a0 a1) evm (mintTransition.body.drop 8 |>.take 4)
      (.ok (mintAmountsFrame v a a0 a1) evm) := by
  have h0 : evalExpr? config (mintResultFrame v a a0 a1) evm
      (.tupleGet (.var "__c1") 1) = .ok (.int a0) := by
    have hg : (mintResultFrame v a a0 a1).locals.get? "__c1" =
        some (.tuple [.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (modifyPositionKey (mintModifyArgs a))), .int a0, .int a1]) := by
      mint_amounts_get
    simp only [evalExpr?, hg, tupleGetValue?, EvalResult.ofOption, bind, EvalResult.bind,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "amount0Int") (value := .int a0) h0) ?_
  have h1 : evalExpr? config (mintAmount0IntFrame v a a0 a1) evm
      (.tupleGet (.var "__c1") 2) = .ok (.int a1) := by
    have hg : (mintAmount0IntFrame v a a0 a1).locals.get? "__c1" =
        some (.tuple [.fixedBytes ⟨31, by decide⟩
          (EVM.Word.toBytesBE (modifyPositionKey (mintModifyArgs a))), .int a0, .int a1]) := by
      mint_amounts_get
    simp only [evalExpr?, hg, tupleGetValue?, EvalResult.ofOption, bind, EvalResult.bind,
      List.getElem?_cons_succ, List.getElem?_cons_zero]
  refine ExecBlock.consNormal (ExecStmt.letDecl (name := "amount1Int") (value := .int a1) h1) ?_
  have h0i : evalExpr? config (mintIntsFrame v a a0 a1) evm (.var "amount0Int") =
      .ok (.int a0) := evalExpr_var_get (by mint_amounts_get)
  refine ExecBlock.consNormal (solm := mintIntsFrame v a a0 a1)
    (ExecStmt.assign (value := .int (Int.ofNat (EVM.wordOfInt a0).toNat))
    (by simp only [evalExpr?, h0i, castValue?, bind, EvalResult.bind,
          EvalResult.ofOption, normalizeUInt256_int])
    (assignLocalVarBase_frame (old := .int 0) (by mint_amounts_get))) ?_
  have h1i : evalExpr? config (mintAmount0Frame v a a0 a1) evm (.var "amount1Int") =
      .ok (.int a1) := evalExpr_var_get (by mint_amounts_get)
  exact ExecBlock.consNormal (solm := mintAmount0Frame v a a0 a1)
    (ExecStmt.assign (value := .int (Int.ofNat (EVM.wordOfInt a1).toNat))
    (by simp only [evalExpr?, h1i, castValue?, bind, EvalResult.bind,
          EvalResult.ofOption, normalizeUInt256_int])
    (assignLocalVarBase_frame (old := .int 0) (by mint_amounts_get))) ExecBlock.nil

end Benchmarks.UniswapV3.Pool
