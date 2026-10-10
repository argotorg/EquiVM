import Benchmarks.UniswapV3.Pool.NextSqrt0Denominator

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def nextSqrt0FastBody : List Stmt :=
  [.internalCall "FullMath_mulDivRoundingUp" nextSqrt0FullArgs "__c0",
    .return [.cast (.var "__c0") (.elem (.int (.uint ⟨160, by decide⟩)))]]

theorem nextSqrt0FastReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = true) (hv : nextSqrt0FullValid a) :
    ExecBlock config (nextSqrt0DenominatorFrame imms a) evm nextSqrt0FastBody
      (.returned (nextSqrt0FullFrame imms a) evm (some [.int (Int.ofNat
        (UInt256.land (nextSqrt0FullResult a) (UInt256.ofNat (2 ^ 160 - 1))).toNat)])) := by
  have hc := nextSqrt0FullReturns imms evm a hv
  simp only [nextSqrt0FullCallName, ha, if_true] at hc
  refine ExecBlock.consNormal hc (ExecBlock.consReturn (ExecStmt.return ?_))
  have he : evalExpr? config (nextSqrt0FullFrame imms a) evm (.var "__c0") =
      .ok (.int (Int.ofNat (nextSqrt0FullResult a).toNat)) :=
    evalExpr_var_get (by
      simp only [nextSqrt0FullFrame, nextSqrt0FullCallName, ha, if_true]
      exact Std.HashMap.getElem?_insert_self)
  have hcast := evalExpr_intCast (.uint ⟨160, by decide⟩) he
  rw [normalizeUIntWord_mask ⟨160, by decide⟩ _
    (UInt256.ofNat (2 ^ 160 - 1)) (by decide)] at hcast
  simp only [evalExprs?, hcast, bind, EvalResult.bind, pure]

theorem nextSqrt0FastReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = true) (hv : ¬nextSqrt0FullValid a) :
    ExecBlock config (nextSqrt0DenominatorFrame imms a) evm nextSqrt0FastBody .reverted := by
  apply ExecBlock.consRevert
  simpa only [nextSqrt0FullCallName, ha, if_true] using nextSqrt0FullReverts imms evm a hv

noncomputable def nextSqrt0CastFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt0FullFrame imms a with
    locals := (nextSqrt0FullFrame imms a).locals.insert "__c4"
      (.int (Int.ofNat (nextSqrt0FullResult a).toNat))}

theorem evalNextSqrt0CastArgs (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = false) :
    evalExprs? config (nextSqrt0FullFrame imms a) evm [.var "__c3"] =
      .ok [.int (Int.ofNat (nextSqrt0FullResult a).toNat)] := by
  have he : evalExpr? config (nextSqrt0FullFrame imms a) evm (.var "__c3") =
      .ok (.int (Int.ofNat (nextSqrt0FullResult a).toNat)) :=
    evalExpr_var_get (by
      simp only [nextSqrt0FullFrame, nextSqrt0FullCallName, ha, Bool.false_eq_true, if_false]
      exact Std.HashMap.getElem?_insert_self)
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem nextSqrt0CastReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = false) (hv : safeCast160Valid (nextSqrt0FullResult a)) :
    ExecStmt config (nextSqrt0FullFrame imms a) evm
      (.internalCall "SafeCast_toUint160" [.var "__c3"] "__c4")
      (.ok (nextSqrt0CastFrame imms a) evm) :=
  internalCallFunctionReturn (callee := safeCast160Function)
    (locals := safeCast160Locals (nextSqrt0FullResult a))
    (calleeSolm := safeCast160ReadyFrame imms (nextSqrt0FullResult a))
    (value := some [.int (Int.ofNat (nextSqrt0FullResult a).toNat)])
    (evalNextSqrt0CastArgs imms evm a ha) safeCast160Lookup (safeCast160Bind _)
    (safeCast160Returns imms evm _ hv)

theorem nextSqrt0CastReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = false) (hv : ¬safeCast160Valid (nextSqrt0FullResult a)) :
    ExecStmt config (nextSqrt0FullFrame imms a) evm
      (.internalCall "SafeCast_toUint160" [.var "__c3"] "__c4") .reverted :=
  internalCallFunctionRevert (callee := safeCast160Function)
    (locals := safeCast160Locals (nextSqrt0FullResult a))
    (evalNextSqrt0CastArgs imms evm a ha) safeCast160Lookup (safeCast160Bind _)
    (safeCast160Reverts imms evm _ hv)

theorem nextSqrt0FullCastReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = false) (hv : nextSqrt0FullValid a)
    (hc : safeCast160Valid (nextSqrt0FullResult a)) :
    ExecBlock config (nextSqrt0DenominatorFrame imms a) evm ((nextSqrt0Branch false).drop 4)
      (.returned (nextSqrt0CastFrame imms a) evm
        (some [.int (Int.ofNat (nextSqrt0FullResult a).toNat)])) := by
  have hf := nextSqrt0FullReturns imms evm a hv
  simp only [nextSqrt0FullCallName, ha, Bool.false_eq_true, if_false] at hf
  refine ExecBlock.consNormal hf (ExecBlock.consNormal (nextSqrt0CastReturns imms evm a ha hc)
    (ExecBlock.consReturn (ExecStmt.return ?_)))
  have he : evalExpr? config (nextSqrt0CastFrame imms a) evm (.var "__c4") =
      .ok (.int (Int.ofNat (nextSqrt0FullResult a).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem nextSqrt0FullCastReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = false) (hv : ¬(nextSqrt0FullValid a ∧
      safeCast160Valid (nextSqrt0FullResult a))) :
    ExecBlock config (nextSqrt0DenominatorFrame imms a) evm ((nextSqrt0Branch false).drop 4)
      .reverted := by
  by_cases hf : nextSqrt0FullValid a
  · have hs := nextSqrt0FullReturns imms evm a hf
    simp only [nextSqrt0FullCallName, ha, Bool.false_eq_true, if_false] at hs
    exact ExecBlock.consNormal hs
      (ExecBlock.consRevert (nextSqrt0CastReverts imms evm a ha (fun hc ↦ hv ⟨hf, hc⟩)))
  · apply ExecBlock.consRevert
    simpa only [nextSqrt0FullCallName, ha, Bool.false_eq_true, if_false]
      using nextSqrt0FullReverts imms evm a hf

end Benchmarks.UniswapV3.Pool
