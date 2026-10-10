import Benchmarks.UniswapV4PoolManager.NextAmount1QuotientSource
import Benchmarks.UniswapV4PoolManager.NextAmount1TailSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev nextAmount1Function : FunctionDecl := contract.functions[117]!
theorem nextAmount1_lookup : lookupCallable? contract "SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown" =
    some nextAmount1Function.toCallable := rfl

theorem nextAmount1_body_eq : nextAmount1Function.body =
    [.letDecl "quotient" (some abiUInt256) (.intLit 0),
     .ite (.var "add") (nextAmount1QuotientStmt true :: nextAmount1TailStmts true)
       (nextAmount1QuotientStmt false :: nextAmount1TailStmts false)] := rfl

theorem nextAmount1Body {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256} {add : Bool}
    (hf : f.contract = contract) (hp : price.toNat < 2^160) (hn : liquidity ≠ ⟨0⟩)
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (ha : f.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)))
    (hb : f.locals.get? "add" = some (.bool add)) :
    ∃ f', ExecFuncBody config f evm nextAmount1Function.body
      (if nextAmount1Fits price liquidity amount add then
        .returned f' evm (some [.int (Int.ofNat (nextAmount1Word price liquidity amount add).toNat)])
       else .reverted) := by
  let f0 := wordLocal f "quotient" ⟨0⟩
  have h0 : ExecStmt config f evm (.letDecl "quotient" (some abiUInt256) (.intLit 0)) (.ok f0 evm) :=
    ExecStmt.letDecl (by simp only [evalExpr?, pure]; rfl)
  have hs0 : f0.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)) :=
    (store_get_ne _ _ (by decide : ("quotient" == "sqrtPX96") = false)).trans hs
  have hl0 : f0.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)) :=
    (store_get_ne _ _ (by decide : ("quotient" == "liquidity") = false)).trans hl
  have ha0 : f0.locals.get? "amount" = some (.int (Int.ofNat amount.toNat)) :=
    (store_get_ne _ _ (by decide : ("quotient" == "amount") = false)).trans ha
  have hb0 : f0.locals.get? "add" = some (.bool add) :=
    (store_get_ne _ _ (by decide : ("quotient" == "add") = false)).trans hb
  have hquot := nextAmount1QuotientSource (f := f0) (evm := evm) add hf hn hl0 ha0 (store_get_self _ _ _)
  rw [nextAmount1_body_eq]
  by_cases hqfit : nextAmount1QuotientFits liquidity amount add
  · rw [if_pos hqfit] at hquot
    let f1 := nextAmount1QuotientFrame f0 liquidity amount add
    have hs1 : f1.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)) :=
      (nextAmount1QuotientFrame_get f0 liquidity amount add "sqrtPX96" (by decide) (by decide)).trans hs0
    obtain ⟨f2, htail⟩ := nextAmount1TailSource (f := f1) (evm := evm) add hf hp hs1 (store_get_self _ _ _)
    simp only [nextAmount1Fits, hqfit, true_and, nextAmount1Word]
    cases add with
    | false =>
      simp only [Bool.false_eq_true, if_false] at htail ⊢
      by_cases ho : (nextAmount1Quotient liquidity amount false).toNat < price.toNat
      · rw [if_pos ho] at htail
        simp only [if_pos ho]
        exact ⟨f2, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consReturn
          (ExecStmt.iteFalse (evalLocalValue hb0) (ExecBlock.consNormal hquot htail))))⟩
      · rw [if_neg ho] at htail
        simp only [if_neg ho]
        exact ⟨f2, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consRevert
          (ExecStmt.iteFalse (evalLocalValue hb0) (ExecBlock.consNormal hquot htail))))⟩
    | true =>
      simp only [if_true] at htail ⊢
      by_cases ho : price.toNat+(nextAmount1Quotient liquidity amount true).toNat < 2^160
      · rw [if_pos ho] at htail
        simp only [if_pos ho]
        exact ⟨f2, ExecFuncBody.execBlockRet (ExecBlock.consNormal h0 (ExecBlock.consReturn
          (ExecStmt.iteTrue (evalLocalValue hb0) (ExecBlock.consNormal hquot htail))))⟩
      · rw [if_neg ho] at htail
        simp only [if_neg ho]
        exact ⟨f2, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consRevert
          (ExecStmt.iteTrue (evalLocalValue hb0) (ExecBlock.consNormal hquot htail))))⟩
  · rw [if_neg hqfit] at hquot
    simp only [nextAmount1Fits, hqfit, false_and, if_false]
    cases add with
    | false => exact ⟨f0, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consRevert
        (ExecStmt.iteFalse (evalLocalValue hb0) (ExecBlock.consRevert hquot))))⟩
    | true => exact ⟨f0, ExecFuncBody.execBlockRevert (ExecBlock.consNormal h0 (ExecBlock.consRevert
        (ExecStmt.iteTrue (evalLocalValue hb0) (ExecBlock.consRevert hquot))))⟩

theorem nextAmount1Call {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256} {add : Bool}
    {es el ea eb : Expr} (hf : f.contract = contract) (hp : price.toNat < 2^160) (hn : liquidity ≠ ⟨0⟩)
    (hs : evalExpr? config f evm es = .ok (.int (Int.ofNat price.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat)))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.bool add)) (ret : Ident) :
    ExecStmt config f evm
      (.internalCall "SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown" [es, el, ea, eb] ret)
      (if nextAmount1Fits price liquidity amount add then
        .ok (wordLocal f ret (nextAmount1Word price liquidity amount add)) evm else .reverted) := by
  let fc : Frame := {f with locals := (((((∅ : Store).insert "add" (.bool add)).insert
    "amount" (.int (Int.ofNat amount.toNat))).insert "liquidity" (.int (Int.ofNat liquidity.toNat))).insert
      "sqrtPX96" (.int (Int.ofNat price.toNat)))}
  have hargs : evalExprs? config f evm [es, el, ea, eb] =
      .ok [.int (Int.ofNat price.toNat), .int (Int.ofNat liquidity.toNat), .int (Int.ofNat amount.toNat), .bool add] := by
    simp only [evalExprs?, hs, hl, ha, hb, bind, EvalResult.bind, pure]
  obtain ⟨f', hbody⟩ := nextAmount1Body (f := fc) (evm := evm) hf hp hn
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("sqrtPX96" == "liquidity") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("liquidity" == "amount") = false)
      (by decide : ("sqrtPX96" == "amount") = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by decide : ("amount" == "add") = false)
      (by decide : ("liquidity" == "add") = false) (by decide : ("sqrtPX96" == "add") = false)).trans
        (store_get_self _ _ _))
  have hlookup : lookupCallable? f.contract "SqrtPriceMath_getNextSqrtPriceFromAmount1RoundingDown" =
      some nextAmount1Function.toCallable := by rw [hf]; exact nextAmount1_lookup
  by_cases hfit : nextAmount1Fits price liquidity amount add
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
