import Benchmarks.UniswapV4PoolManager.NextPriceCalcSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def nextPriceFunction (input : Bool) : FunctionDecl :=
  if input then contract.functions[114]! else contract.functions[115]!
def nextPriceName (input : Bool) : Ident :=
  if input then "SqrtPriceMath_getNextSqrtPriceFromInput" else "SqrtPriceMath_getNextSqrtPriceFromOutput"
def nextPriceAmountName (input : Bool) : Ident := if input then "amountIn" else "amountOut"

theorem nextPrice_lookup (input : Bool) : lookupCallable? contract (nextPriceName input) =
    some (nextPriceFunction input).toCallable := by cases input <;> rfl

def nextPriceGuardExpr : Expr :=
  .binary .and (.binary .ne (.var "sqrtPX96") (.intLit 0))
    (.binary .ne (.var "liquidity") (.intLit 0))

theorem nextPrice_body_eq (input : Bool) : (nextPriceFunction input).body =
    [.require nextPriceGuardExpr,
     .ite (.var "zeroForOne") (nextPriceReturnStmts (nextPriceAmountName input) input input)
       (nextPriceReturnStmts (nextPriceAmountName input) (!input) input)] := by
  cases input <;> rfl

theorem nextPriceGuardSource {f : Frame} {evm : EVM.State} {price liquidity : UInt256}
    (hp : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat))) :
    evalExpr? config f evm nextPriceGuardExpr = .ok (.bool (decide (nextPriceValid price liquidity))) := by
  have hz : evalExpr? config f evm (.intLit 0) = .ok (.int (Int.ofNat (⟨0⟩ : UInt256).toNat)) := by
    simp only [evalExpr?, pure]; rfl
  have he := evalAndBool (evalNeWords (evalLocalValue hp) hz) (evalNeWords (evalLocalValue hl) hz)
  simpa only [nextPriceValid, nextPriceGuardExpr, Bool.decide_and] using he

theorem nextPriceBody {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256}
    (input zeroForOne : Bool) (hf : f.contract = contract) (hp : price.toNat < 2^160)
    (hs : f.locals.get? "sqrtPX96" = some (.int (Int.ofNat price.toNat)))
    (hl : f.locals.get? "liquidity" = some (.int (Int.ofNat liquidity.toNat)))
    (ha : f.locals.get? (nextPriceAmountName input) = some (.int (Int.ofNat amount.toNat)))
    (hb : f.locals.get? "zeroForOne" = some (.bool zeroForOne)) :
    ∃ f', ExecFuncBody config f evm (nextPriceFunction input).body
      (if nextPriceFits price liquidity amount input zeroForOne then
        .returned f' evm (some [.int (Int.ofNat (nextPriceWord price liquidity amount input zeroForOne).toNat)])
       else .reverted) := by
  rw [nextPrice_body_eq]
  have hg := nextPriceGuardSource (f := f) (evm := evm) hs hl
  by_cases hv : nextPriceValid price liquidity
  · have hreq : ExecStmt config f evm (.require nextPriceGuardExpr) (.ok f evm) :=
      ExecStmt.requireTrue (by simpa only [decide_eq_true hv] using hg)
    have hbranch : ExecStmt config f evm
        (.ite (.var "zeroForOne") (nextPriceReturnStmts (nextPriceAmountName input) input input)
          (nextPriceReturnStmts (nextPriceAmountName input) (!input) input))
        (if nextPriceCalcFits price liquidity amount (if zeroForOne then input else !input) input then
          .returned (wordLocal f "result" (nextPriceWord price liquidity amount input zeroForOne)) evm
            (some [.int (Int.ofNat (nextPriceWord price liquidity amount input zeroForOne).toNat)])
         else .reverted) := by
      cases zeroForOne with
      | false =>
        exact ExecStmt.iteFalse (evalLocalValue hb)
          (nextPriceReturnSource (nextPriceAmountName input) (!input) input hf hp hv hs hl ha)
      | true =>
        exact ExecStmt.iteTrue (evalLocalValue hb)
          (nextPriceReturnSource (nextPriceAmountName input) input input hf hp hv hs hl ha)
    refine ⟨wordLocal f "result" (nextPriceWord price liquidity amount input zeroForOne), ?_⟩
    simp only [nextPriceFits, hv, true_and]
    by_cases hfit : nextPriceCalcFits price liquidity amount (if zeroForOne then input else !input) input
    · rw [if_pos hfit] at hbranch ⊢
      exact ExecFuncBody.execBlockRet (ExecBlock.consNormal hreq (ExecBlock.consReturn hbranch))
    · rw [if_neg hfit] at hbranch ⊢
      exact ExecFuncBody.execBlockRevert (ExecBlock.consNormal hreq (ExecBlock.consRevert hbranch))
  · simp only [nextPriceFits, hv, false_and, if_false]
    exact ⟨f, ExecFuncBody.execBlockRevert (ExecBlock.consRevert
      (ExecStmt.requireFalse (by simpa only [decide_eq_false hv] using hg)))⟩

theorem nextPriceCall {f : Frame} {evm : EVM.State} {price liquidity amount : UInt256}
    {es el ea eb : Expr} (input zeroForOne : Bool) (hf : f.contract = contract) (hp : price.toNat < 2^160)
    (hs : evalExpr? config f evm es = .ok (.int (Int.ofNat price.toNat)))
    (hl : evalExpr? config f evm el = .ok (.int (Int.ofNat liquidity.toNat)))
    (ha : evalExpr? config f evm ea = .ok (.int (Int.ofNat amount.toNat)))
    (hb : evalExpr? config f evm eb = .ok (.bool zeroForOne)) (ret : Ident) :
    ExecStmt config f evm (.internalCall (nextPriceName input) [es, el, ea, eb] ret)
      (if nextPriceFits price liquidity amount input zeroForOne then
        .ok (wordLocal f ret (nextPriceWord price liquidity amount input zeroForOne)) evm else .reverted) := by
  let fc : Frame := {f with locals := (((((∅ : Store).insert "zeroForOne" (.bool zeroForOne)).insert
    (nextPriceAmountName input) (.int (Int.ofNat amount.toNat))).insert
      "liquidity" (.int (Int.ofNat liquidity.toNat))).insert "sqrtPX96" (.int (Int.ofNat price.toNat)))}
  have hargs : evalExprs? config f evm [es, el, ea, eb] =
      .ok [.int (Int.ofNat price.toNat), .int (Int.ofNat liquidity.toNat),
        .int (Int.ofNat amount.toNat), .bool zeroForOne] := by
    simp only [evalExprs?, hs, hl, ha, hb, bind, EvalResult.bind, pure]
  obtain ⟨f', hbody⟩ := nextPriceBody (f := fc) (evm := evm) input zeroForOne hf hp
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("sqrtPX96" == "liquidity") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by cases input <;> decide : ("liquidity" == nextPriceAmountName input) = false)
      (by cases input <;> decide : ("sqrtPX96" == nextPriceAmountName input) = false)).trans (store_get_self _ _ _))
    ((store_get_ne3 _ _ _ _ (by cases input <;> decide : (nextPriceAmountName input == "zeroForOne") = false)
      (by decide : ("liquidity" == "zeroForOne") = false)
      (by decide : ("sqrtPX96" == "zeroForOne") = false)).trans (store_get_self _ _ _))
  have hlookup : lookupCallable? f.contract (nextPriceName input) = some (nextPriceFunction input).toCallable := by
    rw [hf]; exact nextPrice_lookup input
  have hbind : bindParams? (nextPriceFunction input).params
      [.int (Int.ofNat price.toNat), .int (Int.ofNat liquidity.toNat),
        .int (Int.ofNat amount.toNat), .bool zeroForOne] = some fc.locals := by
    cases input <;> rfl
  by_cases hfit : nextPriceFits price liquidity amount input zeroForOne
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup hbind hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup hbind hbody

end Benchmarks.UniswapV4PoolManager
