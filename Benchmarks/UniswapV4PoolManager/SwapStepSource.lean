import Benchmarks.UniswapV4PoolManager.SwapStepPreludeSource
import Benchmarks.UniswapV4PoolManager.SwapStepResultSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem swapStep_body_eq : swapStepFunction.body = swapStepFunction.body.take 7 ++
    [.ite (.var "exactIn") swapStepInputStmts swapStepOutputStmts, swapStepReturnStmt] := rfl

theorem swapStepBody {f : Frame} {evm : EVM.State} {price target liquidity remaining fee : UInt256}
    (hc : f.contract = contract) (hp : price.toNat < 2^160) (ht : target.toNat < 2^160)
    (hs : f.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)))
    (htr : f.locals.get? "sqrtPriceTargetX96" = some (.int (Int.ofNat target.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (hr : f.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)))
    (hf : f.locals.get? "feePips" = some (.int (Int.ofNat fee.toNat))) :
    ∃ f', ExecFuncBody config f evm swapStepFunction.body
      (if swapStepFits price target liquidity remaining fee then
        .returned f' evm (some (swapStepReturnValues (swapStepWord price target liquidity remaining fee))) else .reverted) := by
  rw [swapStep_body_eq]
  let f0 := swapStepPreludeFrame f price target remaining fee
  let dir := swapStepDirection price target
  have hpre := swapStepPreludeSource (evm := evm) hs htr hr hf
  have hc0 : f0.contract = contract := (swapStepPreludeFrame_contract _ _ _ _ _).trans hc
  have hs0 : f0.locals.get? "sqrtPriceCurrentX96" = some (.int (Int.ofNat price.toNat)) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte, hs]
  have ht0 : f0.locals.get? "sqrtPriceTargetX96" = some (.int (Int.ofNat target.toNat)) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte, htr]
  have hl0 : f0.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte, hl]
  have hr0 : f0.locals.get? "amountRemaining" = some (.int (EVM.signed remaining)) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte, hr]
  have hf0 : f0.locals.get? "_feePips" = some (.int (Int.ofNat fee.toNat)) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hb0 : f0.locals.get? "zeroForOne" = some (.bool dir) := by
    simp only [f0, dir, swapStepPreludeFrame_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hn0 : f0.locals.get? "sqrtPriceNextX96" = some (.int 0) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
  have hi0 : f0.locals.get? "amountIn" = some (.int 0) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
  have ho0 : f0.locals.get? "amountOut" = some (.int 0) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
  have hfa0 : f0.locals.get? "feeAmount" = some (.int 0) := by
    simp only [f0, swapStepPreludeFrame_get, swapStepPreludeWordsFrame, wordLocal_get,
      beq_iff_eq, String.reduceEq, ↓reduceIte]; rfl
  have hexact : evalExpr? config f0 evm (.var "exactIn") = .ok (.bool (swapStepExactInput remaining)) :=
    evalLocalValue (store_get_self _ _ _)
  cases he : swapStepExactInput remaining with
  | false =>
    let f1 := swapStepOutputFrame f0 price target liquidity remaining fee dir
    refine ⟨f1, ?_⟩
    simp only [swapStepFits, swapStepWord, he, Bool.false_eq_true, if_false]
    have hbranch := swapStepOutputSource (f := f0) (evm := evm) dir hc0 hp ht hs0 ht0 hl0 hr0 hf0 hb0 hn0 hi0 ho0 hfa0
    have hg : evalExpr? config f0 evm (.var "exactIn") = .ok (.bool false) := by simpa only [he] using hexact
    by_cases hfit : swapStepOutputFits price target liquidity remaining fee dir
    · rw [if_pos hfit] at hbranch ⊢
      exact execFuncBody_prepend hpre (ExecFuncBody.execBlockRet (ExecBlock.consNormal
        (ExecStmt.iteFalse hg hbranch) (swapStepReturnSource (swapStepOutputFrame_result _ _ _ _ _ _ _))))
    · rw [if_neg hfit] at hbranch ⊢
      exact execFuncBody_prepend hpre (ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.iteFalse hg hbranch)))
  | true =>
    let f1 := swapStepInputFrame f0 price target liquidity remaining fee dir
    refine ⟨f1, ?_⟩
    simp only [swapStepFits, swapStepWord, he, if_true]
    have hbranch := swapStepInputSource (f := f0) (evm := evm) dir hc0 hp ht hs0 ht0 hl0 hr0 hf0 hb0 hn0 hi0 ho0 hfa0
    have hg : evalExpr? config f0 evm (.var "exactIn") = .ok (.bool true) := by simpa only [he] using hexact
    by_cases hfit : swapStepInputFits price target liquidity remaining fee dir
    · rw [if_pos hfit] at hbranch ⊢
      exact execFuncBody_prepend hpre (ExecFuncBody.execBlockRet (ExecBlock.consNormal
        (ExecStmt.iteTrue hg hbranch) (swapStepReturnSource (swapStepInputFrame_result _ _ _ _ _ _ _))))
    · rw [if_neg hfit] at hbranch ⊢
      exact execFuncBody_prepend hpre (ExecFuncBody.execBlockRevert (ExecBlock.consRevert
        (ExecStmt.iteTrue hg hbranch)))

def swapStepCallFrame (f : Frame) (ret : Ident) (w : SwapStepWords) : Frame :=
  {f with locals := f.locals.insert ret (.tuple (swapStepReturnValues w))}

theorem swapStepCall {f : Frame} {evm : EVM.State} {price target liquidity remaining fee : UInt256}
    {ep et el er ef : Expr} (hc : f.contract = contract) (hp : price.toNat < 2^160) (ht : target.toNat < 2^160)
    (hep : evalExpr? config f evm ep = .ok (.int (Int.ofNat price.toNat)))
    (het : evalExpr? config f evm et = .ok (.int (Int.ofNat target.toNat)))
    (hel : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat)))
    (her : evalExpr? config f evm er = .ok (.int (EVM.signed remaining)))
    (hef : evalExpr? config f evm ef = .ok (.int (Int.ofNat fee.toNat))) (ret : Ident) :
    ExecStmt config f evm (.internalCall "SwapMath_computeSwapStep" [ep, et, el, er, ef] ret)
      (if swapStepFits price target liquidity remaining fee then
        .ok (swapStepCallFrame f ret (swapStepWord price target liquidity remaining fee)) evm else .reverted) := by
  let fc : Frame := {f with locals := ((((((∅ : Store).insert "feePips" (.int (Int.ofNat fee.toNat))).insert
    "amountRemaining" (.int (EVM.signed remaining))).insert "liquidity" (.int (Int.ofNat liquidity.toNat))).insert
      "sqrtPriceTargetX96" (.int (Int.ofNat target.toNat))).insert "sqrtPriceCurrentX96" (.int (Int.ofNat price.toNat)))}
  have hargs : evalExprs? config f evm [ep, et, el, er, ef] =
      .ok [.int (Int.ofNat price.toNat), .int (Int.ofNat target.toNat), .int (Int.ofNat liquidity.toNat),
        .int (EVM.signed remaining), .int (Int.ofNat fee.toNat)] := by
    simp only [evalExprs?, hep, het, hel, her, hef, bind, EvalResult.bind, pure]
  obtain ⟨f', hbody⟩ := swapStepBody (f := fc) (evm := evm) hc hp ht
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("sqrtPriceCurrentX96" == "sqrtPriceTargetX96") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("sqrtPriceTargetX96" == "liquidity") = false)
      (by decide : ("sqrtPriceCurrentX96" == "liquidity") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("liquidity" == "amountRemaining") = false)
      (by decide : ("sqrtPriceTargetX96" == "amountRemaining") = false)
      (by decide : ("sqrtPriceCurrentX96" == "amountRemaining") = false)).trans (store_get_self _ _ _))
    ((store_get_ne4 _ _ _ _ _ (by decide : ("amountRemaining" == "feePips") = false)
      (by decide : ("liquidity" == "feePips") = false)
      (by decide : ("sqrtPriceTargetX96" == "feePips") = false)
      (by decide : ("sqrtPriceCurrentX96" == "feePips") = false)).trans (store_get_self _ _ _))
  have hlookup : lookupCallable? f.contract "SwapMath_computeSwapStep" = some swapStepFunction.toCallable := by
    rw [hc]; exact swapStep_lookup
  by_cases hfit : swapStepFits price target liquidity remaining fee
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
