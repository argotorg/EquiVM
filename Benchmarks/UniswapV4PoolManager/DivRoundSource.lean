import Benchmarks.UniswapV4PoolManager.DivRoundWords
import Benchmarks.UniswapV4PoolManager.WordModSource
import Benchmarks.UniswapV4PoolManager.WordBorrowSource
import Benchmarks.UniswapV4PoolManager.WordLocals
import Benchmarks.UniswapV4PoolManager.PoolCheckSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev divRoundFunction : FunctionDecl := contract.functions[107]!
theorem divRound_lookup : lookupCallable? contract "UnsafeMath_divRoundingUp" =
    some divRoundFunction.toCallable := rfl

theorem evalDivRound {cfg : Config} {f : Frame} {evm : EVM.State} {ex ey : Expr} {x y : UInt256}
    (hx : evalExpr? cfg f evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? cfg f evm ey = .ok (.int (Int.ofNat y.toNat))) (hn : y ≠ ⟨0⟩) :
    evalExpr? cfg f evm (.binary .add (.binary .div ex ey)
      (.ite (.binary .gt (.binary .mod ex ey) (.intLit 0)) (.intLit 1) (.intLit 0))) =
      .ok (.int (Int.ofNat (divRoundWord x y).toNat)) := by
  have hdiv := evalWordDiv hx hy hn
  have hmod := evalWordMod hx hy hn
  have hgt := evalWordGt hmod
    (show evalExpr? cfg f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  have he := naturalAddSource hdiv (evalBoolWord hgt)
  have hyn : y.toNat ≠ 0 := fun h => hn (uint256_toNat_eq_zero h)
  have hb : (UInt256.fromBool (decide ((⟨0⟩ : UInt256).toNat < (UInt256.mod x y).toNat))).toNat =
      if 0 < x.toNat%y.toNat then 1 else 0 := by
    rw [wordMod_toNat hyn]
    change (UInt256.fromBool (decide (0 < x.toNat%y.toNat))).toNat = _
    split <;> simp only [*, decide_true, decide_false, UInt256.fromBool] <;> rfl
  simpa only [divRoundWord_toNat hn, udiv_toNat, hb] using he

theorem divRoundBody {f : Frame} {evm : EVM.State} {x y : UInt256}
    (hx : f.locals.get? "x" = some (.int (Int.ofNat x.toNat)))
    (hy : f.locals.get? "y" = some (.int (Int.ofNat y.toNat))) :
    ∃ f', ExecFuncBody config f evm divRoundFunction.body
      (.returned f' evm (some [.int (Int.ofNat (divRoundWord x y).toNat)])) := by
  let f0 := wordLocal f "z" ⟨0⟩
  have h0 : ExecStmt config f evm divRoundFunction.body[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hx0 : f0.locals.get? "x" = some (.int (Int.ofNat x.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hx]
  have hy0 : f0.locals.get? "y" = some (.int (Int.ofNat y.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hy]
  have heq := evalEqWords (evalLocalValue (cfg := config) (f := f0) (evm := evm) hy0)
    (show evalExpr? config f0 evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  by_cases hz : y = ⟨0⟩
  · rw [hz, divRoundWord_zero]
    exact ⟨f0, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consReturn
      (ExecStmt.iteTrue (by simpa only [decide_eq_true hz] using heq)
        (ABlock.start.returns (by simp only [evalExpr?, pure]; rfl)))))⟩
  · let f1 := wordLocal f0 "z" (divRoundWord x y)
    have h1 : ExecStmt config f0 evm divRoundFunction.body[1]! (.ok f0 evm) :=
      ExecStmt.iteFalse (by simpa only [decide_eq_false hz] using heq) ExecBlock.nil
    have h2 : ExecStmt config f0 evm divRoundFunction.body[2]! (.ok f1 evm) :=
      ExecStmt.assign (evalDivRound (evalLocalValue hx0) (evalLocalValue hy0) hz)
        (assignLocalValue (store_get_self _ _ _))
    exact ⟨f1, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
      (ExecBlock.consNormal h2 (ABlock.start.returns wordLocal_eval))))⟩

theorem divRoundCall {f : Frame} {evm : EVM.State} {x y : UInt256} {ex ey : Expr}
    (hf : f.contract = contract)
    (hx : evalExpr? config f evm ex = .ok (.int (Int.ofNat x.toNat)))
    (hy : evalExpr? config f evm ey = .ok (.int (Int.ofNat y.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "UnsafeMath_divRoundingUp" [ex, ey] ret)
      (.ok (wordLocal f ret (divRoundWord x y)) evm) := by
  let fc : Frame := {f with locals := (((∅ : Store).insert "y" (.int (Int.ofNat y.toNat))).insert
    "x" (.int (Int.ofNat x.toNat)))}
  obtain ⟨f', hbody⟩ := divRoundBody (f := fc) (evm := evm) (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("x" == "y") = false)).trans (store_get_self _ _ _))
  have hargs : evalExprs? config f evm [ex, ey] =
      .ok [.int (Int.ofNat x.toNat), .int (Int.ofNat y.toNat)] := by
    simp only [evalExprs?, hx, hy, bind, EvalResult.bind, pure]
  exact internalCallFunctionReturn hargs (by rw [hf]; exact divRound_lookup) rfl hbody

end Benchmarks.UniswapV4PoolManager
