import Benchmarks.UniswapV3.Pool.NextSqrt0FullSource
import Benchmarks.UniswapV3.Pool.NextSqrt0FallbackCalls

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem nextSqrt0FastChoiceReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = true) (hn : a.amount.toNat ≠ 0) (hs : nextSqrt0Fast a)
    (hv : nextSqrt0FullValid a) :
    ExecStmt config (nextSqrt0ProductFrame imms a) evm (nextSqrt0Branch true)[2]!
      (.returned (nextSqrt0FullFrame imms a) evm (some [.int (Int.ofNat
        (UInt256.land (nextSqrt0FullResult a) (UInt256.ofNat (2 ^ 160 - 1))).toNat)])) := by
  have hp := evalNextSqrt0ProductGuard imms evm a hn
  have hd := nextSqrt0DenominatorSource imms evm a
  have hg := evalNextSqrt0DenominatorGuard imms evm a
  have hge : (nextSqrt0Numerator a).toNat ≤ (nextSqrt0Denominator a).toNat := by
    simpa only [nextSqrt0Denominator, ha, if_true] using hs.2
  simp only [ha] at hd
  apply ExecStmt.iteTrue (by simpa only [hs.1, decide_true] using hp)
  exact ExecBlock.consNormal hd (ExecBlock.consReturn (ExecStmt.iteTrue
    (by simpa only [hge, decide_true] using hg) (nextSqrt0FastReturns imms evm a ha hv)))

theorem nextSqrt0FastChoiceReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = true) (hn : a.amount.toNat ≠ 0) (hs : nextSqrt0Fast a)
    (hv : ¬nextSqrt0FullValid a) :
    ExecStmt config (nextSqrt0ProductFrame imms a) evm (nextSqrt0Branch true)[2]!
      .reverted := by
  have hp := evalNextSqrt0ProductGuard imms evm a hn
  have hd := nextSqrt0DenominatorSource imms evm a
  have hg := evalNextSqrt0DenominatorGuard imms evm a
  have hge : (nextSqrt0Numerator a).toNat ≤ (nextSqrt0Denominator a).toNat := by
    simpa only [nextSqrt0Denominator, ha, if_true] using hs.2
  simp only [ha] at hd
  apply ExecStmt.iteTrue (by simpa only [hs.1, decide_true] using hp)
  exact ExecBlock.consNormal hd (ExecBlock.consRevert (ExecStmt.iteTrue
    (by simpa only [hge, decide_true] using hg) (nextSqrt0FastReverts imms evm a ha hv)))

theorem nextSqrt0FallbackChoice (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (ha : a.add = true) (hn : a.amount.toNat ≠ 0) (hs : ¬nextSqrt0Fast a) :
    ExecStmt config (nextSqrt0ProductFrame imms a) evm (nextSqrt0Branch true)[2]!
      (.ok (nextSqrt0FallbackFrame imms a) evm) := by
  have hp := evalNextSqrt0ProductGuard imms evm a hn
  by_cases he : nextSqrt0ProductExact a
  · have hd := nextSqrt0DenominatorSource imms evm a
    have hg := evalNextSqrt0DenominatorGuard imms evm a
    have hge : ¬(nextSqrt0Numerator a).toNat ≤ (nextSqrt0Denominator a).toNat := by
      intro h
      apply hs ⟨he, ?_⟩
      simpa only [nextSqrt0Denominator, ha, if_true] using h
    simp only [ha] at hd
    rw [nextSqrt0FallbackFrame, if_pos he]
    apply ExecStmt.iteTrue (by simpa only [he, decide_true] using hp)
    exact ExecBlock.consNormal hd (ExecBlock.consNormal
      (ExecStmt.iteFalse (by simpa only [hge, decide_false] using hg) ExecBlock.nil) ExecBlock.nil)
  · rw [nextSqrt0FallbackFrame, if_neg he]
    exact ExecStmt.iteFalse (by simpa only [he, decide_false] using hp) ExecBlock.nil

theorem nextSqrt0FallbackReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : nextSqrt0FallbackValid a) :
    ExecBlock config (nextSqrt0FallbackFrame imms a) evm ((nextSqrt0Branch true).drop 3)
      (.returned (nextSqrt0FallbackDivFrame imms a) evm (some [.int (Int.ofNat
        (UInt256.land (unsafeDivRoundResult (nextSqrt0Numerator a) (nextSqrt0FallbackSum a))
          (UInt256.ofNat (2 ^ 160 - 1))).toNat)])) := by
  refine ExecBlock.consNormal (nextSqrt0FallbackAddReturns imms evm a hv)
    (ExecBlock.consNormal (nextSqrt0FallbackDivReturns imms evm a)
      (ExecBlock.consReturn (ExecStmt.return ?_)))
  have he : evalExpr? config (nextSqrt0FallbackDivFrame imms a) evm (.var "__c2") =
      .ok (.int (Int.ofNat
        (unsafeDivRoundResult (nextSqrt0Numerator a) (nextSqrt0FallbackSum a)).toNat)) :=
    evalExpr_var_get Std.HashMap.getElem?_insert_self
  have hc := evalExpr_intCast (.uint ⟨160, by decide⟩) he
  rw [normalizeUIntWord_mask ⟨160, by decide⟩ _ (UInt256.ofNat (2 ^ 160 - 1)) (by decide)] at hc
  simp only [evalExprs?, hc, bind, EvalResult.bind, pure]

end Benchmarks.UniswapV3.Pool
