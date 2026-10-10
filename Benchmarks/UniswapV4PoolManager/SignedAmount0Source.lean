import Benchmarks.UniswapV4PoolManager.SignedAmount0Path

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

abbrev signedAmount0Function : FunctionDecl := contract.functions[70]!
theorem signedAmount0_lookup : lookupCallable? contract "SqrtPriceMath_getAmount0Delta" =
    some signedAmount0Function.toCallable := rfl

theorem signedAmount0Body {f : Frame} {evm : EVM.State} {a b : UInt256} {delta : Int}
    (hf : f.contract = contract) (ha : a.toNat < 2^160) (hb : b.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hea : f.locals.get? "sqrtPriceAX96" = some (.int (Int.ofNat a.toNat)))
    (heb : f.locals.get? "sqrtPriceBX96" = some (.int (Int.ofNat b.toNat)))
    (hed : f.locals.get? "liquidity" = some (.int delta)) :
    ∃ f', ExecFuncBody config f evm signedAmount0Function.body
      (if signedAmount0Fits a b delta then
        .returned f' evm (some [.int (EVM.signed (signedAmount0Word a b delta))]) else .reverted) := by
  exact signedAmountBody (fits := fun r => amount0Fits a b (liquidityMagnitude delta) r)
    (word := fun r => amount0Word a b (liquidityMagnitude delta) r) hdlo hdhi hed
    (fun _ r he => signedAmount0Path hf ha hb hea heb he r)

theorem signedAmount0Call {f : Frame} {evm : EVM.State} {a b : UInt256} {delta : Int} {ea eb ed : Expr}
    (hf : f.contract = contract) (ha : a.toNat < 2^160) (hb : b.toNat < 2^160)
    (hdlo : -(2^127 : Int) ≤ delta) (hdhi : delta < 2^127)
    (hea : evalExpr? config f evm ea = .ok (.int (Int.ofNat a.toNat)))
    (heb : evalExpr? config f evm eb = .ok (.int (Int.ofNat b.toNat)))
    (hed : evalExpr? config f evm ed = .ok (.int delta)) (ret : Ident) :
    ExecStmt config f evm (.internalCall "SqrtPriceMath_getAmount0Delta" [ea, eb, ed] ret)
      (if signedAmount0Fits a b delta then
        .ok {f with locals := f.locals.insert ret (.int (EVM.signed (signedAmount0Word a b delta)))} evm
       else .reverted) := by
  let fc : Frame := {f with locals := ((((∅ : Store).insert "liquidity" (.int delta)).insert
    "sqrtPriceBX96" (.int (Int.ofNat b.toNat))).insert "sqrtPriceAX96" (.int (Int.ofNat a.toNat)))}
  obtain ⟨f', hbody⟩ := signedAmount0Body (f := fc) (evm := evm) hf ha hb hdlo hdhi
    (store_get_self _ _ _)
    ((store_get_ne _ _ (by decide : ("sqrtPriceAX96" == "sqrtPriceBX96") = false)).trans (store_get_self _ _ _))
    ((store_get_ne2 _ _ _ (by decide : ("sqrtPriceBX96" == "liquidity") = false)
      (by decide : ("sqrtPriceAX96" == "liquidity") = false)).trans (store_get_self _ _ _))
  have hargs : evalExprs? config f evm [ea, eb, ed] =
      .ok [.int (Int.ofNat a.toNat), .int (Int.ofNat b.toNat), .int delta] := by
    simp only [evalExprs?, hea, heb, hed, bind, EvalResult.bind, pure]
  have hlookup : lookupCallable? f.contract "SqrtPriceMath_getAmount0Delta" =
      some signedAmount0Function.toCallable := by rw [hf]; exact signedAmount0_lookup
  by_cases hfit : signedAmount0Fits a b delta
  · rw [if_pos hfit] at hbody ⊢
    exact internalCallFunctionReturn hargs hlookup rfl hbody
  · rw [if_neg hfit] at hbody ⊢
    exact internalCallFunctionRevert hargs hlookup rfl hbody

end Benchmarks.UniswapV4PoolManager
