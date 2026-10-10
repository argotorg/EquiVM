import Benchmarks.UniswapV3.Pool.NextSqrt1QuotientSource
import Benchmarks.UniswapV3.Pool.LowGasSafeAdd

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt1QuotientGet (imms : Store) (a : NextSqrtArgs) :
    (nextSqrt1QuotientFrame imms a).locals.get? "sqrtPX96" =
        some (.int (Int.ofNat a.price.toNat)) ∧
      (nextSqrt1QuotientFrame imms a).locals.get? "quotient" =
        some (.int (Int.ofNat (nextSqrt1Quotient a).toNat)) := by
  cases ha : a.add <;> by_cases hs : nextSqrt1Small a <;>
    simp only [nextSqrt1QuotientFrame, nextSqrt1ChosenFrame, nextSqrt1Direct,
      nextSqrt1CallFrame, nextSqrt1CallName, nextSqrt1ZeroFrame, nextSqrt1CondName,
      nextSqrtFrame, nextSqrtLocals, hs, ha, Bool.false_eq_true, ↓reduceIte,
      and_false, and_true, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] <;> exact ⟨rfl, rfl⟩

noncomputable def nextSqrt1AddFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt1QuotientFrame imms a with
    locals := (nextSqrt1QuotientFrame imms a).locals.insert "__c2"
      (.int (Int.ofNat (a.price + nextSqrt1Quotient a).toNat))}

noncomputable def nextSqrt1CastFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  {nextSqrt1AddFrame imms a with
    locals := (nextSqrt1AddFrame imms a).locals.insert "__c3"
      (.int (Int.ofNat (a.price + nextSqrt1Quotient a).toNat))}

def nextSqrt1AddArgs : List Expr :=
  [.cast (.var "sqrtPX96") (.elem (.int (.uint ⟨256, by decide⟩))), .var "quotient"]

theorem evalNextSqrt1AddArgs (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExprs? config (nextSqrt1QuotientFrame imms a) evm nextSqrt1AddArgs =
      .ok [.int (Int.ofNat a.price.toNat), .int (Int.ofNat (nextSqrt1Quotient a).toNat)] := by
  have ep := evalExpr_intCast (.uint ⟨256, by decide⟩)
    (evalExpr_var_get (cfg := config) (evm := evm) (nextSqrt1QuotientGet imms a).1)
  rw [normalizeInt_uint256_word] at ep
  have eq := evalExpr_var_get (cfg := config) (evm := evm) (nextSqrt1QuotientGet imms a).2
  simp only [nextSqrt1AddArgs, evalExprs?, ep, eq, bind, EvalResult.bind, pure]

theorem nextSqrt1AddReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : a.price.toNat ≤ (a.price + nextSqrt1Quotient a).toNat) :
    ExecStmt config (nextSqrt1QuotientFrame imms a) evm
      (.internalCall "LowGasSafeMath_add" nextSqrt1AddArgs "__c2")
      (.ok (nextSqrt1AddFrame imms a) evm) :=
  internalCallFunctionReturn (callee := safeAddFunction)
    (locals := safeAddLocals a.price (nextSqrt1Quotient a))
    (calleeSolm := safeAddResultFrame imms a.price (nextSqrt1Quotient a))
    (value := some [.int (Int.ofNat (a.price + nextSqrt1Quotient a).toNat)])
    (evalNextSqrt1AddArgs imms evm a) safeAddLookup (safeAddBind _ _)
    (safeAddReturns imms evm _ _ hv)

theorem nextSqrt1AddReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬a.price.toNat ≤ (a.price + nextSqrt1Quotient a).toNat) :
    ExecStmt config (nextSqrt1QuotientFrame imms a) evm
      (.internalCall "LowGasSafeMath_add" nextSqrt1AddArgs "__c2") .reverted :=
  internalCallFunctionRevert (callee := safeAddFunction)
    (locals := safeAddLocals a.price (nextSqrt1Quotient a))
    (evalNextSqrt1AddArgs imms evm a) safeAddLookup (safeAddBind _ _)
    (safeAddReverts imms evm _ _ hv)

theorem evalNextSqrt1CastArgs (imms : Store) (evm : EVM.State) (a : NextSqrtArgs) :
    evalExprs? config (nextSqrt1AddFrame imms a) evm [.var "__c2"] =
      .ok [.int (Int.ofNat (a.price + nextSqrt1Quotient a).toNat)] := by
  have he : evalExpr? config (nextSqrt1AddFrame imms a) evm (.var "__c2") =
      .ok (.int (Int.ofNat (a.price + nextSqrt1Quotient a).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  simp only [evalExprs?, he, bind, EvalResult.bind, pure]

theorem nextSqrt1CastReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : safeCast160Valid (a.price + nextSqrt1Quotient a)) :
    ExecStmt config (nextSqrt1AddFrame imms a) evm
      (.internalCall "SafeCast_toUint160" [.var "__c2"] "__c3")
      (.ok (nextSqrt1CastFrame imms a) evm) :=
  internalCallFunctionReturn (callee := safeCast160Function)
    (locals := safeCast160Locals (a.price + nextSqrt1Quotient a))
    (calleeSolm := safeCast160ReadyFrame imms (a.price + nextSqrt1Quotient a))
    (value := some [.int (Int.ofNat (a.price + nextSqrt1Quotient a).toNat)])
    (evalNextSqrt1CastArgs imms evm a) safeCast160Lookup (safeCast160Bind _)
    (safeCast160Returns imms evm _ hv)

theorem nextSqrt1CastReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬safeCast160Valid (a.price + nextSqrt1Quotient a)) :
    ExecStmt config (nextSqrt1AddFrame imms a) evm
      (.internalCall "SafeCast_toUint160" [.var "__c2"] "__c3") .reverted :=
  internalCallFunctionRevert (callee := safeCast160Function)
    (locals := safeCast160Locals (a.price + nextSqrt1Quotient a))
    (evalNextSqrt1CastArgs imms evm a) safeCast160Lookup (safeCast160Bind _)
    (safeCast160Reverts imms evm _ hv)

end Benchmarks.UniswapV3.Pool
