import Benchmarks.UniswapV4PoolManager.SignedAmount1Path

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev signedAmount1Function : FunctionDecl := contract.functions[72]!
theorem signedAmount1_lookup : lookupCallable? contract "SqrtPriceMath_getAmount1Delta" =
    some signedAmount1Function.toCallable := rfl

theorem signedAmount1Body {f : Frame} {evm : EVM.State} {a b : UInt256} {delta : Int}
    (hf : f.contract = contract)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hea : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)))
    (heb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat)))
    (hed : f.locals.get? "liquidity" = some (.int delta)) :
    ∃ f', ExecFuncBody config f evm signedAmount1Function.body
      (if signedAmount1Fits a b delta then
        .returned f' evm (some [.int (EVM.signed (signedAmount1Word a b delta))]) else .reverted) := by
  exact signedAmountBody (fits := fun _ => amount1Fits a b (liquidityMagnitude delta))
    (word := fun r => amount1Word a b (liquidityMagnitude delta) r) hdlo hdhi hed
    (fun _ r he => signedAmount1Path hf hea heb he r)

theorem signedAmount1Call {f : Frame} {evm : EVM.State} {a b : UInt256} {delta : Int} {ea eb ed : Expr}
    (hf : f.contract = contract)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hea : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (heb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hed : evalExpr? config f evm ed = .ok (.int delta)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "SqrtPriceMath_getAmount1Delta" [ea, eb, ed] ret)
      (if signedAmount1Fits a b delta then
        .ok {f with locals := f.locals.insert ret (.int (EVM.signed (signedAmount1Word a b delta)))} evm
       else .reverted) := by
  let fc : Frame := {f with locals := ((((∅ : Store).insert "liquidity" (.int delta)).insert
    "sqrtPriceBX96" (.int (Int.ofNat b.toNat))).insert "sqrtPriceAX96" (.int (Int.ofNat a.toNat)))}
  obtain ⟨f', hbody⟩ := signedAmount1Body (f := fc) (evm := evm) hf hdlo hdhi
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("sqrtPriceAX96" == "sqrtPriceBX96") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("sqrtPriceBX96" == "liquidity") = false)
      (by decide : ("sqrtPriceAX96" == "liquidity") = false)).trans (store_get_self _ _ _))
  have hargs : evalExprs? config f evm [ea, eb, ed] =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int delta] := by
    simp only [evalExprs?, hea, heb, hed, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "SqrtPriceMath_getAmount1Delta" =
      some signedAmount1Function.toCallable := by rw [hf]; exact signedAmount1_lookup
  by_cases hfit : signedAmount1Fits a b delta
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
