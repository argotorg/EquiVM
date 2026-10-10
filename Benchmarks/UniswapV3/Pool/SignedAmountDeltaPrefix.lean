import Benchmarks.UniswapV3.Pool.SignedAmountDeltaModel
import Benchmarks.UniswapV3.Pool.AmountDeltaPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 1000

def signedAmountDeltaZeroFrame (imms : Store) (second : Bool) (a : SignedAmountDeltaArgs) : Frame :=
  let locals := (signedAmountDeltaLocals a).insert (amountDeltaOutputName second) (.int 0)
  {signedAmountDeltaFrame imms a with locals := locals}

def signedAmountDeltaReadyFrame (imms : Store) (second : Bool) (a : SignedAmountDeltaArgs) : Frame :=
  let locals := (signedAmountDeltaZeroFrame imms second a).locals.insert "__cond4" (.int 0)
  {signedAmountDeltaZeroFrame imms second a with locals := locals}

def signedAmountDeltaCallName (a : SignedAmountDeltaArgs) : Ident :=
  if a.liquidity < 0 then "__c0" else "__c2"

def signedAmountDeltaCastName (a : SignedAmountDeltaArgs) : Ident :=
  if a.liquidity < 0 then "__c1" else "__c3"

noncomputable def signedAmountDeltaCallFrame (imms : Store) (second : Bool)
    (a : SignedAmountDeltaArgs) : Frame :=
  let locals := (signedAmountDeltaReadyFrame imms second a).locals.insert (signedAmountDeltaCallName a)
    (.int (Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat))
  {signedAmountDeltaReadyFrame imms second a with locals := locals}

noncomputable def signedAmountDeltaCastFrame (imms : Store) (second : Bool)
    (a : SignedAmountDeltaArgs) : Frame :=
  let locals := (signedAmountDeltaCallFrame imms second a).locals.insert (signedAmountDeltaCastName a)
    (.int (Int.ofNat (amountDeltaResult second (signedAmountDeltaUnsigned a)).toNat))
  {signedAmountDeltaCallFrame imms second a with locals := locals}

noncomputable def signedAmountDeltaReturnFrame (imms : Store) (second : Bool)
    (a : SignedAmountDeltaArgs) : Frame :=
  let locals := (signedAmountDeltaCastFrame imms second a).locals.insert "__cond4"
    (.int (signedAmountDeltaResult second a))
  {signedAmountDeltaCastFrame imms second a with locals := locals}

macro "signed_amount_delta_get" : tactic =>
  `(tactic| (simp only [signedAmountDeltaReturnFrame, signedAmountDeltaCastFrame,
    signedAmountDeltaCallFrame, signedAmountDeltaReadyFrame, signedAmountDeltaZeroFrame,
    signedAmountDeltaFrame, signedAmountDeltaLocals, signedAmountDeltaCastName,
    signedAmountDeltaCallName, amountDeltaOutputName]; (try split_ifs) <;>
      (simp only [Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]; rfl)))

theorem signedAmountDeltaPrefixSource (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) :
    ExecBlock config (signedAmountDeltaFrame imms a) evm
      ((signedAmountDeltaFunction second).body.take 2)
      (.ok (signedAmountDeltaReadyFrame imms second a) evm) := by
  cases second <;>
    exact ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure]))
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?, pure])) ExecBlock.nil)

def signedAmountDeltaCallArgs (a : SignedAmountDeltaArgs) : List Expr :=
  [.var "sqrtRatioAX96", .var "sqrtRatioBX96",
    if a.liquidity < 0 then
      .cast (.cast (.binary .sub (.intLit 0) (.var "liquidity"))
        (.elem (.int (.sint ⟨128, by decide⟩)))) (.elem (.int (.uint ⟨128, by decide⟩)))
    else .cast (.var "liquidity") (.elem (.int (.uint ⟨128, by decide⟩))),
    .boolLit (decide (0 ≤ a.liquidity))]

theorem evalSignedAmountDeltaArgs (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) (hfit : a.Fits) :
    evalExprs? config (signedAmountDeltaReadyFrame imms second a) evm
      (signedAmountDeltaCallArgs a) =
      .ok [.int (Int.ofNat a.sqrtA.toNat), .int (Int.ofNat a.sqrtB.toNat),
        .int (Int.ofNat (signedAmountDeltaUnsigned a).liquidity.toNat),
        .bool (signedAmountDeltaUnsigned a).roundUp] := by
  have ha : evalExpr? config (signedAmountDeltaReadyFrame imms second a) evm (.var "sqrtRatioAX96") =
      .ok (.int (Int.ofNat a.sqrtA.toNat)) := evalExpr_var_get (by signed_amount_delta_get)
  have hb : evalExpr? config (signedAmountDeltaReadyFrame imms second a) evm (.var "sqrtRatioBX96") =
      .ok (.int (Int.ofNat a.sqrtB.toNat)) := evalExpr_var_get (by signed_amount_delta_get)
  have hl : evalExpr? config (signedAmountDeltaReadyFrame imms second a) evm (.var "liquidity") =
      .ok (.int a.liquidity) := evalExpr_var_get (by signed_amount_delta_get)
  by_cases hn : a.liquidity < 0
  · simp only [signedAmountDeltaCallArgs, if_pos hn, evalExprs?, evalExpr?, ha, hb, hl,
      bind, EvalResult.bind, evalBinaryOp?, castValue?, EvalResult.ofOption, pure,
      signedAmountDeltaNegativeCast a hfit hn]
    rfl
  · simp only [signedAmountDeltaCallArgs, if_neg hn, evalExprs?, evalExpr?, ha, hb, hl,
      bind, EvalResult.bind, castValue?, EvalResult.ofOption, pure,
      signedAmountDeltaPositiveCast a hfit hn]
    rfl

theorem evalSignedAmountDeltaGuard (imms : Store) (evm : EVM.State) (second : Bool)
    (a : SignedAmountDeltaArgs) :
    evalExpr? config (signedAmountDeltaReadyFrame imms second a) evm
      (.binary .lt (.var "liquidity") (.intLit 0)) = .ok (.bool (decide (a.liquidity < 0))) := by
  have hl : evalExpr? config (signedAmountDeltaReadyFrame imms second a) evm (.var "liquidity") =
      .ok (.int a.liquidity) := evalExpr_var_get (by signed_amount_delta_get)
  simp only [evalExpr?, hl, bind, EvalResult.bind, evalBinaryOp?, pure]

end Benchmarks.UniswapV3.Pool
