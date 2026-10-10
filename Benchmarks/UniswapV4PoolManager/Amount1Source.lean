import Benchmarks.UniswapV4PoolManager.Amount1TailSource
import Benchmarks.UniswapV4PoolManager.AbsDiffSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem amount1Body {f : Frame} {evm : EVM.State} {a b liquidity : UInt256} {roundUp : Bool}
    (hf : f.contract = contract)
    (ha : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? "roundUp" = some (.bool roundUp)) :
    ∃ f', ExecFuncBody config f evm amount1Function.body
      (if amount1Fits a b liquidity then
        .returned f' evm (some [.int (Int.ofNat (amount1Word a b liquidity roundUp).toNat)])
       else .reverted) := by
  let f0 := wordLocal f "amount1" ⟨0⟩
  let f1 := wordLocal f0 "numerator" (absDiffWord a b)
  let f2 := wordLocal f1 "denominator" fullMathQ96
  let f3 := wordLocal f2 "_liquidity" liquidity
  have h0 : ExecStmt config f evm amount1Function.body[0]! (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have ha0 : f0.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha]
  have hb0 : f0.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat)) := by
    simp only [f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb]
  have h1 : ExecStmt config f0 evm amount1Function.body[1]! (.ok f1 evm) :=
    absDiffCall (f := f0) hf (evalLocalValue ha0) (evalLocalValue hb0) _
  have h2 : ExecStmt config f1 evm amount1Function.body[2]! (.ok f2 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hl2 : f2.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)) := by
    simp only [f2, f1, f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hl]
  have hcast := evalExpr_cast_int (intType := .uint ⟨256, by decide⟩)
    (evalLocalValue (cfg := config) (f := f2) (evm := evm) hl2)
  rw [normalizeInt_uint256_word] at hcast
  have h3 : ExecStmt config f2 evm amount1Function.body[3]! (.ok f3 evm) := ExecStmt.letDecl hcast
  have hn3 : f3.locals.get? "numerator" = some (.int (Int.ofNat (absDiffWord a b).toNat)) := by
    simp only [f3, f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hd3 : f3.locals.get? "denominator" = some (.int (Int.ofNat fullMathQ96.toNat)) := by
    simp only [f3, f2, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have h4 := fullMathCall (f := f3) (evm := evm) hf wordLocal_eval
    (evalLocalValue hn3) (evalLocalValue hd3) "__c1"
  have hpre : ExecBlock config f evm (amount1Function.body.take 4) (.ok f3 evm) :=
    ExecBlock.consNormal h0 (ExecBlock.consNormal h1 (ExecBlock.consNormal h2 (execBlock_singleton h3)))
  by_cases hfit : amount1Fits a b liquidity
  · rw [if_pos hfit] at h4
    simp only [if_pos hfit]
    let f4 := wordLocal f3 "__c1" (fullMathWord liquidity (absDiffWord a b) fullMathQ96)
    let f5 := wordLocal f4 "amount1" (fullMathWord liquidity (absDiffWord a b) fullMathQ96)
    have ha4 : f4.locals.get? "amount1" = some (.int 0) := by
      simp only [f4, f3, f2, f1, f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
    have h5 : ExecStmt config f4 evm amount1Function.body[5]! (.ok f5 evm) :=
      ExecStmt.assign wordLocal_eval (assignLocalValue ha4)
    have ht := amount1Tail (f := f5) (evm := evm) (a := a) (b := b) (liquidity := liquidity) (roundUp := roundUp)
      (by simp only [f5, f4, f3, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte])
      (by simp only [f5, f4, f3, f2, f1, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte])
      (by simp only [f5, f4, f3, f2, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte])
      (store_get_self _ _ _)
      (by simp only [f5, f4, f3, f2, f1, f0, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hr])
    exact ⟨_, execFuncBody_prepend hpre
      (execFuncBody_prepend (ExecBlock.consNormal h4 (execBlock_singleton h5)) ht)⟩
  · rw [if_neg hfit] at h4
    simp only [if_neg hfit]
    exact ⟨f3, execFuncBody_prepend hpre (ExecFuncBody.execBlockRevert (ExecBlock.consRevert h4))⟩

theorem amount1Call {f : Frame} {evm : EVM.State} {a b liquidity : UInt256} {roundUp : Bool}
    {ea eb el er : Expr} (hf : f.contract = contract)
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat)))
    (hr : evalExpr? config f evm er = .ok (.bool roundUp)) (ret : Ident) :
    ExecStmt config f evm
      (.internalCall "SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool" [ea, eb, el, er] ret)
      (if amount1Fits a b liquidity then .ok (wordLocal f ret (amount1Word a b liquidity roundUp)) evm
       else .reverted) := by
  let fc : Frame := {f with locals := (((((∅ : Store).insert "roundUp" (.bool roundUp)).insert
    "liquidity" (.int (Int.ofNat liquidity.toNat))).insert "sqrtPriceBX96" (.int (Int.ofNat b.toNat))).insert
    "sqrtPriceAX96" (.int (Int.ofNat a.toNat)))}
  have ha' : fc.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)) := store_get_self _ _ _
  have hb' : fc.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat)) :=
    (store_get_ne _ _ (by decide : ("sqrtPriceAX96" == "sqrtPriceBX96") = false)).trans (store_get_self _ _ _)
  have hl' : fc.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)) := by
    simp only [fc, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hr' : fc.locals.get? "roundUp" = some (.bool roundUp) := by
    simp only [fc, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_iff_eq, String.reduceEq, ↓reduceIte]
  obtain ⟨f', hbody⟩ := amount1Body (f := fc) (evm := evm) hf ha' hb' hl' hr'
  have hargs : evalExprs? config f evm [ea, eb, el, er] =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int (Int.ofNat liquidity.toNat), .bool roundUp] := by
    simp only [evalExprs?, ha, hb, hl, hr, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "SqrtPriceMath_getAmount1Delta_uint160_uint160_uint128_bool" =
      some amount1Function.toCallable := by rw [hf]; exact amount1_lookup
  by_cases hfit : amount1Fits a b liquidity
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
