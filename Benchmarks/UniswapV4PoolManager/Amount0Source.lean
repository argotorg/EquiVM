import Benchmarks.UniswapV4PoolManager.Amount0Branches

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem amount0CoreBody {f : Frame} {evm : EVM.State} {lo hi liquidity : UInt256} {roundUp : Bool}
    (hf : f.contract = contract) (ho : lo.toNat ≤ hi.toNat) (hh : hi.toNat < 2^160)
    (ha : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat lo.toNat)))
    (hb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat hi.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? "roundUp" = some (.bool roundUp)) :
    ∃ f', ExecFuncBody config f evm (amount0Function.body.drop 1)
      (if amount0CoreFits lo hi liquidity roundUp then
        .returned f' evm (some [.int (Int.ofNat (amount0CoreWord lo hi liquidity roundUp).toNat)])
       else .reverted) := by
  have hguard := evalNeWords (evalLocalValue (cfg := config) (f := f) (evm := evm) ha)
    (show evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) by
      simp only [evalExpr?, pure]; rfl)
  by_cases hz : lo = ⟨0⟩
  · have hn : ¬amount0CoreFits lo hi liquidity roundUp := fun hh => hh.1 hz
    simp only [if_neg hn]
    exact ⟨f, ExecFuncBody.execBlockRevert (ExecBlock.consRevert
      (ExecStmt.requireFalse (by simpa only [hz, ne_self_iff_false, decide_false] using hguard)))⟩
  · have h1 : ExecStmt config f evm amount0Function.body[1]! (.ok f evm) :=
      ExecStmt.requireTrue (by simpa only [decide_eq_true hz] using hguard)
    have hn := amount0Numerators (evm := evm) ho hh ha hb hl
    let fn := amount0NumeratorsFrame f lo hi liquidity
    obtain ⟨f', hbranch⟩ := amount0Branches (f := fn) (evm := evm) (roundUp := roundUp) (liquidity := liquidity) hf hz
      (by simp only [fn, amount0NumeratorsFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, ha])
      (by simp only [fn, amount0NumeratorsFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hb])
      (by simp only [fn, amount0NumeratorsFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte])
      (store_get_self _ _ _)
      (by simp only [fn, amount0NumeratorsFrame, wordLocal_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hr])
    by_cases hfit : amount0CoreFits lo hi liquidity roundUp
    · rw [if_pos hfit] at hbranch
      simp only [if_pos hfit]
      exact ⟨f', execFuncBody_prepend (ExecBlock.consNormal h1 hn)
        (ExecFuncBody.execBlockRet (ExecBlock.consReturn hbranch))⟩
    · rw [if_neg hfit] at hbranch
      simp only [if_neg hfit]
      exact ⟨f', execFuncBody_prepend (ExecBlock.consNormal h1 hn)
        (ExecFuncBody.execBlockRevert (ExecBlock.consRevert hbranch))⟩

theorem amount0Body {f : Frame} {evm : EVM.State} {a b liquidity : UInt256} {roundUp : Bool}
    (hf : f.contract = contract) (hac : a.toNat < 2^160) (hbc : b.toNat < 2^160)
    (ha : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)))
    (hb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? "roundUp" = some (.bool roundUp)) :
    ∃ f', ExecFuncBody config f evm amount0Function.body
      (if amount0Fits a b liquidity roundUp then
        .returned f' evm (some [.int (Int.ofNat (amount0Word a b liquidity roundUp).toNat)])
       else .reverted) := by
  have hs := amount0Sort (evm := evm) ha hb
  have hp := amount0SortFrame_prices ha hb
  obtain ⟨f', hc⟩ := amount0CoreBody (evm := evm)
    ((amount0SortFrame_contract _ _ _).trans hf) (amount0_ordered a b) (amount0_bounds hac hbc).2
    hp.1 hp.2
    ((amount0SortFrame_get _ _ _ _ (by decide) (by decide) (by decide) (by decide)).trans hl)
    ((amount0SortFrame_get _ _ _ _ (by decide) (by decide) (by decide) (by decide)).trans hr)
  exact ⟨f', execFuncBody_prepend (execBlock_singleton hs) hc⟩

theorem amount0Call {f : Frame} {evm : EVM.State} {a b liquidity : UInt256} {roundUp : Bool}
    {ea eb el er : Expr} (hf : f.contract = contract) (hac : a.toNat < 2^160) (hbc : b.toNat < 2^160)
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat)))
    (hr : evalExpr? config f evm er = .ok (.bool roundUp)) (ret : Ident) :
    ExecStmt config f evm
      (.internalCall "SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool" [ea, eb, el, er] ret)
      (if amount0Fits a b liquidity roundUp then .ok (wordLocal f ret (amount0Word a b liquidity roundUp)) evm
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
  obtain ⟨f', hbody⟩ := amount0Body (f := fc) (evm := evm) hf hac hbc ha' hb' hl' hr'
  have hargs : evalExprs? config f evm [ea, eb, el, er] =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int (Int.ofNat liquidity.toNat), .bool roundUp] := by
    simp only [evalExprs?, ha, hb, hl, hr, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "SqrtPriceMath_getAmount0Delta_uint160_uint160_uint128_bool" =
      some amount0Function.toCallable := by rw [hf]; exact amount0_lookup
  by_cases hfit : amount0Fits a b liquidity roundUp
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
