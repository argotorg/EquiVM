import Benchmarks.CompoundIII.Comet.QuoteSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def quoteArgs (I : ExecutionEnv) : Store :=
  (((∅ : Store).insert "asset" (.address (AccountAddress.ofNat
    (calldataWord I.calldata 4).toNat))).insert "baseAmount"
      (.int (calldataWord I.calldata 36).toNat))

theorem quoteCollateralTransition_body : quoteCollateralTransition.body = calldataPrologue
    [.internalCall "quoteCollateral_body" [.var "asset", .var "baseAmount"] "__r",
      .return [.var "__r"]] := rfl

theorem quoteCollateral_source {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) {result : Option (EVM.State × UInt256)}
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (ht : QuoteTrace v (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)
      (calldataWord I.calldata 36) (initState σ σ₀ g A I) result) :
    match result with
    | none => ExecTransitionBody config contract (initState σ σ₀ g A I) (quoteArgs I)
        quoteCollateralTransition.body .reverted (immStore v)
    | some (evm', value) => ∃ final,
        ExecTransitionBody config contract (initState σ σ₀ g A I) (quoteArgs I)
          quoteCollateralTransition.body (.returned final evm' (some [.int value.toNat]))
          (immStore v) := by
  let frame := calldataLocalFrame
    { contract := contract, locals := quoteArgs I, immutables := immStore v }
    (initState σ σ₀ g A I)
  have ha : evalExpr? config frame (initState σ σ₀ g A I) (.var "asset") =
      .ok (.address (AccountAddress.ofNat (calldataWord I.calldata 4).toNat)) := by
    simp only [evalExpr?, frame, calldataLocalFrame, quoteArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hb : evalExpr? config frame (initState σ σ₀ g A I) (.var "baseAmount") =
      .ok (.int (calldataWord I.calldata 36).toNat) := by
    simp only [evalExpr?, frame, calldataLocalFrame, quoteArgs, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have hs := quote_call ht frame _ _ "__r" rfl rfl ha hb
  cases result with
  | none =>
      rw [quoteCollateralTransition_body]
      apply ExecFuncBody.execBlockRevert
      exact (calldataPrologue_ok hv hhi).run (ExecBlock.consRevert hs)
  | some r =>
      obtain ⟨evm', value⟩ := r
      refine ⟨{ frame with locals := frame.locals.insert "__r" (.int value.toNat) }, ?_⟩
      rw [quoteCollateralTransition_body]
      apply ExecFuncBody.execBlockRet
      apply (calldataPrologue_ok hv hhi).run
      exact ExecBlock.consNormal hs (ABlock.start.returns (by
        simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption]
        rfl))

end Benchmarks.CompoundIII.Comet
