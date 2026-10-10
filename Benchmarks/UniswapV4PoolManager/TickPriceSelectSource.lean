import Benchmarks.UniswapV4PoolManager.TickPriceWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

-- LIBRARY CANDIDATE: inequality of signed word-valued source expressions.
theorem evalNeSignedWords {cfg : Config} {f : Frame} {evm : EVM.State} {lhs rhs : Expr}
    {a b : UInt256}
    (ha : evalExpr? cfg f evm lhs = .ok (.int (EVM.signed a)))
    (hb : evalExpr? cfg f evm rhs = .ok (.int (EVM.signed b))) :
    evalExpr? cfg f evm (.binary .ne lhs rhs) = .ok (.bool (decide (a ≠ b))) := by
  have he : EVM.signed a = EVM.signed b ↔ a = b := signedWord_injective.eq_iff
  simp only [evalExpr?, ha, hb, bind, EvalResult.bind, evalBinaryOp?, BEq.beq,
    Value.int.injEq, he, decide_not]

theorem tickPriceSelectSource {f : Frame} {evm : EVM.State} {sqrtPrice low high : UInt256}
    (hf : f.contract = contract)
    (hs : f.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)))
    (hlow : f.locals.get? "tickLow" = some (.int (EVM.signed low)))
    (hhigh : f.locals.get? "tickHi" = some (.int (EVM.signed high)))
    (ht : f.locals.get? "tick" = some (.int (EVM.signed low))) :
    ∃ f', ExecBlock config f evm (tickPriceFunction.body.drop 53)
      (signedWordResult f' evm (tickPriceChoose sqrtPrice low high)) := by
  have hneq := evalNeSignedWords (cfg := config) (evm := evm) (evalLocalValue hlow) (evalLocalValue hhigh)
  by_cases heq : low = high
  · simp only [signedWordResult, tickPriceChoose, if_pos heq]
    refine ⟨f, (ExecBlock.consNormal
      (ExecStmt.iteFalse ?_ ExecBlock.nil) (ABlock.start.returns (evalLocalValue ht)))⟩
    simpa only [heq, ne_eq, not_true_eq_false, decide_false] using hneq
  · have hcall := tickSqrtCall (f := f) (evm := evm) hf (evalLocalValue hhigh)
        (signedNatAbs_lt_size high) "priceHi"
    by_cases hb : (EVM.signed high).natAbs ≤ 887272
    · rw [if_pos hb] at hcall
      let priceHi := tickSqrtPrice (EVM.signed high)
      let f5 : Frame := {f with locals := f.locals.insert "priceHi" (.int (Int.ofNat priceHi.toNat))}
      have hhigh5 : f5.locals.get? "tickHi" = some (.int (EVM.signed high)) :=
        (store_get_ne _ _ (by decide : ("priceHi" == "tickHi") = false)).trans hhigh
      have hlow5 : f5.locals.get? "tickLow" = some (.int (EVM.signed low)) :=
        (store_get_ne _ _ (by decide : ("priceHi" == "tickLow") = false)).trans hlow
      have hs5 : f5.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat sqrtPrice.toNat)) :=
        (store_get_ne _ _ (by decide : ("priceHi" == "sqrtPriceX96") = false)).trans hs
      have hcmp := evalNatLe (cfg := config) (f := f5) (evm := evm)
        (evalLocalValue (show f5.locals.get? "priceHi" = some (.int (Int.ofNat priceHi.toNat)) from store_get_self _ _ _))
        (evalLocalValue hs5)
      let result := if priceHi.toNat ≤ sqrtPrice.toNat then high else low
      have hselect : evalExpr? config f5 evm (.ite (.binary .le (.var "priceHi") (.var "sqrtPriceX96"))
          (.var "tickHi") (.var "tickLow")) = .ok (.int (EVM.signed result)) := by
        by_cases hc : priceHi.toNat ≤ sqrtPrice.toNat <;>
          simp only [evalExpr?, hcmp, hc, decide_true, decide_false, bind, EvalResult.bind,
            evalLocalValue hhigh5, evalLocalValue hlow5, result, if_true, if_false]
      let f6 : Frame := {f5 with locals := f5.locals.insert "tick" (.int (EVM.signed result))}
      have ht5 : f5.locals.get? "tick" = some (.int (EVM.signed low)) :=
        (store_get_ne _ _ (by decide : ("priceHi" == "tick") = false)).trans ht
      have hbranch : ExecStmt config f evm tickPriceFunction.body[53]! (.ok f6 evm) :=
        ExecStmt.iteTrue (by simpa only [decide_eq_true heq] using hneq)
          (ExecBlock.consNormal hcall (execBlock_singleton (ExecStmt.assign hselect (assignLocalValue ht5))))
      simp only [signedWordResult, tickPriceChoose, if_neg heq, if_pos hb]
      have ht6 : f6.locals.get? "tick" = some (.int (EVM.signed result)) := store_get_self _ _ _
      exact ⟨f6, (ExecBlock.consNormal hbranch
        (ABlock.start.returns (evalLocalValue ht6)))⟩
    · rw [if_neg hb] at hcall
      simp only [signedWordResult, tickPriceChoose, if_neg heq, if_neg hb]
      exact ⟨f, (ExecBlock.consRevert
        (ExecStmt.iteTrue (by simpa only [decide_eq_true heq] using hneq) (ExecBlock.consRevert hcall)))⟩

end Benchmarks.UniswapV4PoolManager
