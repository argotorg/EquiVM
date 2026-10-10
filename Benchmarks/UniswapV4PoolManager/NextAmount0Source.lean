import Benchmarks.UniswapV4PoolManager.NextAmount0AddSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev nextAmount0Function : FunctionDecl := contract.functions[116]!
theorem nextAmount0_lookup : lookupCallable? contract "SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp" =
    some nextAmount0Function.toCallable := rfl

def nextAmount0NumeratorExpr : Expr :=
  .binary (.shl (.uint ⟨256, by decide⟩))
    (.cast (.var "liquidity") (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 96)

theorem nextAmount0_body_eq : nextAmount0Function.body =
    [.ite (.binary .eq (.var "amount") (.intLit 0)) [.return [.var "sqrtPX96"]] [],
     .letDecl "numerator1" (some abiUInt256) nextAmount0NumeratorExpr,
     .ite (.var "add") nextAmount0AddStmts nextAmount0SubStmts] := rfl

theorem nextAmount0Body {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256} {add : Bool}
    (hf : f.contract = contract) (hp : price ≠ ⟨0⟩)
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hb : f.locals.get? "add" = some (.bool add)) :
    ∃ f', ExecFuncBody config f evm nextAmount0Function.body
      (if nextAmount0Fits price liquidity amount add then
        .returned f' evm (some [.int (Int.ofNat (nextAmount0Word price liquidity amount add).toNat)])
       else .reverted) := by
  have hz := evalEqWords (evalLocalValue (cfg := config) (f := f) (evm := evm) ha)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  rw [nextAmount0_body_eq]
  by_cases hzero : amount = ⟨0⟩
  · simp only [nextAmount0Fits, hzero, true_or, if_true, nextAmount0Word]
    exact ⟨f, ExecFuncBody.execBlockRet (ExecBlock.consReturn (ExecStmt.iteTrue
      (by simpa only [decide_eq_true hzero] using hz) (ABlock.start.returns (evalLocalValue hs))))⟩
  · have h0 : ExecStmt config f evm
        (.ite (.binary .eq (.var "amount") (.intLit 0)) [.return [.var "sqrtPX96"]] []) (.ok f evm) :=
      ExecStmt.iteFalse (by simpa only [decide_eq_false hzero] using hz) ExecBlock.nil
    let f1 := wordLocal f "numerator1" (amount0Numerator1 liquidity)
    have hcast := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
      (evalLocalValue (cfg := config) (f := f) (evm := evm) hl)
    rw [normalizeInt_uint256_word] at hcast
    have h1 : ExecStmt config f evm (.letDecl "numerator1" (some abiUInt256) nextAmount0NumeratorExpr) (.ok f1 evm) :=
      ExecStmt.letDecl (evalWordShl (by decide : 96 < 256) hcast (by simp only [evalExpr?, pure]; rfl))
    have hs1 : f1.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)) :=
      (store_get_ne _ _ (by decide : ("numerator1" == "sqrtPX96") = false)).trans hs
    have ha1 : f1.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
      (store_get_ne _ _ (by decide : ("numerator1" == "amount") = false)).trans ha
    have hb1 : f1.locals.get? "add" = some (.bool add) :=
      (store_get_ne _ _ (by decide : ("numerator1" == "add") = false)).trans hb
    simp only [nextAmount0Fits, hzero, false_or, nextAmount0Word, if_false]
    cases add with
    | false =>
      obtain ⟨f2, hr⟩ := nextAmount0SubSource (f := f1) (evm := evm) hf hzero (store_get_self _ _ _) hs1 ha1
      by_cases hfit : nextAmount0CoreFits price liquidity amount false
      · rw [if_pos hfit] at hr
        simp only [if_pos hfit]
        exact ⟨f2, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
          (ExecBlock.consReturn (ExecStmt.iteFalse (evalLocalValue hb1) hr))))⟩
      · rw [if_neg hfit] at hr
        simp only [if_neg hfit]
        exact ⟨f2, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
          (ExecBlock.consRevert (ExecStmt.iteFalse (evalLocalValue hb1) hr))))⟩
    | true =>
      obtain ⟨f2, hr⟩ := nextAmount0AddSource (f := f1) (evm := evm) hf hp hzero (store_get_self _ _ _) hs1 ha1
      by_cases hfit : nextAmount0CoreFits price liquidity amount true
      · rw [if_pos hfit] at hr
        simp only [if_pos hfit]
        exact ⟨f2, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
          (ExecBlock.consReturn (ExecStmt.iteTrue (evalLocalValue hb1) hr))))⟩
      · rw [if_neg hfit] at hr
        simp only [if_neg hfit]
        exact ⟨f2, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consNormal h1
          (ExecBlock.consRevert (ExecStmt.iteTrue (evalLocalValue hb1) hr))))⟩

theorem nextAmount0Call {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256} {add : Bool}
    {es el ea eb : Expr} (hf : f.contract = contract) (hp : price ≠ ⟨0⟩)
    (hs : evalExpr? config f evm es = .ok (.int (Int.ofNat price.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat)))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.bool add)) (ret : Ident) :
    ExecStmt config f evm
      (.internalCall "SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp" [es, el, ea, eb] ret)
      (if nextAmount0Fits price liquidity amount add then
        .ok (wordLocal f ret (nextAmount0Word price liquidity amount add)) evm else .reverted) := by
  let fc : Frame := {f with locals := (((((∅ : Store).insert "add" (.bool add)).insert
    "amount" (.int (Int.ofNat amount.toNat))).insert "liquidity" (.int (Int.ofNat liquidity.toNat))).insert
      "sqrtPX96" (.int (Int.ofNat price.toNat)))}
  have hargs : evalExprs? config f evm [es, el, ea, eb] =
      .ok [.int (Int.ofNat price.toNat), .int (Int.ofNat liquidity.toNat), .int (Int.ofNat amount.toNat), .bool add] := by
    simp only [evalExprs?, hs, hl, ha, hb, bind, EvalResult.bind, pure]
  obtain ⟨f', hbody⟩ := nextAmount0Body (f := fc) (evm := evm) hf hp
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("sqrtPX96" == "liquidity") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("liquidity" == "amount") = false)
      (by decide : ("sqrtPX96" == "amount") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("amount" == "add") = false)
      (by decide : ("liquidity" == "add") = false) (by decide : ("sqrtPX96" == "add") = false)).trans
        (store_get_self _ _ _))
  have hlookup : lookupCallable? f.contract "SqrtPriceMath_getNextSqrtPriceFromAmount0RoundingUp" =
      some nextAmount0Function.toCallable := by rw [hf]; exact nextAmount0_lookup
  by_cases hfit : nextAmount0Fits price liquidity amount add
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
