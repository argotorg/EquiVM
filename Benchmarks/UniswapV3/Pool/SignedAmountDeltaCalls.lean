import Benchmarks.UniswapV3.Pool.SignedAmountDeltaPrefix
import Benchmarks.UniswapV3.Pool.AmountDeltaRoutines
import Benchmarks.UniswapV3.Pool.SafeCast256Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

theorem signedAmountDeltaCallSource (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) (hfit : a.Fits) (hv : signedAmountDeltaValid second a) :
    ExecStmt config (signedAmountDeltaReadyFrame imms second a) evm
      (.internalCall (amountDeltaName second) (signedAmountDeltaCallArgs a) (signedAmountDeltaCallName a))
      (.ok (signedAmountDeltaCallFrame imms second a) evm) := by
  exact internalCallFunctionReturn (callee := amountDeltaFunction second)
    (calleeSolm := amountDeltaReturnFrame imms second (signedAmountDeltaUnsigned a))
    (locals := amountDeltaLocals (signedAmountDeltaUnsigned a))
    (value := some [.int (Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat)])
    (evalSignedAmountDeltaArgs imms evm second a hfit) (amountDeltaLookup second)
    (amountDeltaBind second (signedAmountDeltaUnsigned a))
    (amountDeltaReturns imms evm second _ (signedAmountDeltaUnsignedFits a hfit) hv)

theorem signedAmountDeltaCallReverts (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) (hfit : a.Fits) (hv : ¬signedAmountDeltaValid second a) :
    ExecStmt config (signedAmountDeltaReadyFrame imms second a) evm
      (.internalCall (amountDeltaName second) (signedAmountDeltaCallArgs a) (signedAmountDeltaCallName a))
      .reverted := by
  exact internalCallFunctionRevert (callee := amountDeltaFunction second)
    (locals := amountDeltaLocals (signedAmountDeltaUnsigned a))
    (evalSignedAmountDeltaArgs imms evm second a hfit) (amountDeltaLookup second)
    (amountDeltaBind second (signedAmountDeltaUnsigned a))
    (amountDeltaReverts imms evm second _ (signedAmountDeltaUnsignedFits a hfit) hv)

theorem signedAmountDeltaCastSource (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) (hfit : a.Fits) (hv : signedAmountDeltaValid second a) :
    ExecStmt config (signedAmountDeltaCallFrame imms second a) evm
      (.internalCall "SafeCast_toInt256" [.var (signedAmountDeltaCallName a)] (signedAmountDeltaCastName a))
      (.ok (signedAmountDeltaCastFrame imms second a) evm) := by
  have he : evalExpr? config (signedAmountDeltaCallFrame imms second a) evm
      (.var (signedAmountDeltaCallName a)) =
      .ok (.int (Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  exact internalCallFunctionReturn (callee := safeCast256Function)
    (calleeSolm := safeCast256ReadyFrame imms (amountDeltaResult second (signedAmountDeltaUnsigned a)))
    (locals := safeCast256Locals (amountDeltaResult second (signedAmountDeltaUnsigned a)))
    (value := some [.int (Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat)])
    (by simp only [evalExprs?, he, bind, EvalResult.bind, pure]) safeCast256Lookup (safeCast256Bind _)
    (safeCast256Returns imms evm _
      (amountDeltaResult_lt255 second _ (signedAmountDeltaUnsignedFits a hfit) hv))

def signedAmountDeltaAssignExpr (a : SignedAmountDeltaArgs) : Expr :=
  if a.liquidity < 0 then
    .cast (.binary .sub (.intLit 0) (.var "__c1")) (.elem (.int (.sint ⟨256, by decide⟩)))
  else .var "__c3"

theorem signedAmountDeltaAssignSource (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) (hfit : a.Fits) (hv : signedAmountDeltaValid second a) :
    ExecStmt config (signedAmountDeltaCastFrame imms second a) evm
      (.assign .localVar ⟨"__cond4", []⟩ (signedAmountDeltaAssignExpr a))
      (.ok (signedAmountDeltaReturnFrame imms second a) evm) := by
  have hc : (signedAmountDeltaCastFrame imms second a).locals.get? "__cond4" = some (.int 0) := by
    signed_amount_delta_get
  apply ExecStmt.assign (value := .int (signedAmountDeltaResult second a)) ?_
    (assignLocalVarBase_frame hc)
  have he : evalExpr? config (signedAmountDeltaCastFrame imms second a) evm
      (.var (signedAmountDeltaCastName a)) =
      .ok (.int (Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  by_cases hn : a.liquidity < 0
  · have hb := signedAmountDeltaResult_bounds second a hfit hv
    have hr : normalizeInt (.sint ⟨256, by decide⟩)
        (0 - Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat) =
        signedAmountDeltaResult second a := by
      simp only [signedAmountDeltaResult, if_pos hn] at hb ⊢
      rw [zero_sub]
      exact normalizeSint_eq_self ⟨256, by decide⟩ _ hb.1 hb.2
    simp only [signedAmountDeltaCastName, if_pos hn] at he
    simp only [signedAmountDeltaAssignExpr, if_pos hn, evalExpr?, he, bind, EvalResult.bind,
      evalBinaryOp?, castValue?, EvalResult.ofOption, pure, hr]
  · simpa only [signedAmountDeltaAssignExpr, signedAmountDeltaCastName,
      signedAmountDeltaResult, if_neg hn] using he

end Benchmarks.UniswapV3.Pool
