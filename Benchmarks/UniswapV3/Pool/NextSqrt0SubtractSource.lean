import Benchmarks.UniswapV3.Pool.NextSqrt0FullSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

local instance (a : NextSqrtArgs) : Decidable (nextSqrt0SubtractGuard a) :=
  inferInstanceAs (Decidable (_ ∧ _))

theorem evalNextSqrt0SubtractGuard (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hn : a.amount.toNat ≠ 0) :
    evalExpr? config (nextSqrt0ProductFrame imms a) evm
      (.binary .and nextSqrt0ProductGuardExpr
        (.binary .gt (.var "numerator1") (.var "product"))) =
      .ok (.bool (decide (nextSqrt0SubtractGuard a))) := by
  have en := evalExpr_var_get (cfg := config) (evm := evm)
    (nextSqrt0ProductGet imms a).2.2.2.1
  have ep := evalExpr_var_get (cfg := config) (evm := evm)
    (nextSqrt0ProductGet imms a).2.2.2.2
  have he := evalExpr_bool_and (evalNextSqrt0ProductGuard imms evm a hn) (evalExpr_word_gt en ep)
  simpa only [nextSqrt0SubtractGuard, Bool.decide_and] using he

theorem nextSqrt0SubtractReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = false) (hn : a.amount.toNat ≠ 0) (hs : nextSqrt0SubtractGuard a)
    (hv : nextSqrt0FullValid a) (hc : safeCast160Valid (nextSqrt0FullResult a)) :
    ExecBlock config (nextSqrt0ProductFrame imms a) evm ((nextSqrt0Branch false).drop 2)
      (.returned (nextSqrt0CastFrame imms a) evm (some [.int (Int.ofNat
        (UInt256.land (nextSqrt0FullResult a) (UInt256.ofNat (2 ^ 160 - 1))).toNat)])) := by
  rw [u256LandMaskCleanOfToNat (bits := 160) _ _ (by decide) ((safeCast160Valid_iff _).mp hc)]
  have hd := nextSqrt0DenominatorSource imms evm a
  simp only [ha] at hd
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consNormal hd (nextSqrt0FullCastReturns imms evm a ha hv hc))
  simpa only [hs, decide_true] using evalNextSqrt0SubtractGuard imms evm a hn

theorem nextSqrt0SubtractReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = false) (hn : a.amount.toNat ≠ 0)
    (hv : ¬(nextSqrt0SubtractGuard a ∧ nextSqrt0FullValid a ∧
      safeCast160Valid (nextSqrt0FullResult a))) :
    ExecBlock config (nextSqrt0ProductFrame imms a) evm ((nextSqrt0Branch false).drop 2)
      .reverted := by
  have hg := evalNextSqrt0SubtractGuard imms evm a hn
  by_cases hs : nextSqrt0SubtractGuard a
  · have hd := nextSqrt0DenominatorSource imms evm a
    simp only [ha] at hd
    exact ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [hs, decide_true] using hg))
      (ExecBlock.consNormal hd (nextSqrt0FullCastReverts imms evm a ha (fun h ↦ hv ⟨hs, h⟩)))
  · exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [hs, decide_false] using hg))

end Benchmarks.UniswapV3.Pool
