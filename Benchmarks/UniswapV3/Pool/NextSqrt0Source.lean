import Benchmarks.UniswapV3.Pool.NextSqrt0ChoiceSource
import Benchmarks.UniswapV3.Pool.NextSqrt0SubtractSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

noncomputable def nextSqrt0FinalFrame (imms : Store) (a : NextSqrtArgs) : Frame :=
  if a.amount.toNat = 0 then nextSqrtFrame imms a
  else if a.add then
    if nextSqrt0Fast a then nextSqrt0FullFrame imms a else nextSqrt0FallbackDivFrame imms a
  else nextSqrt0CastFrame imms a

theorem nextSqrt0BranchReturns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hn : a.amount.toNat ≠ 0) (hv : nextSqrt0Valid a) :
    ExecBlock config (nextSqrt0NumeratorFrame imms a) evm (nextSqrt0Branch a.add)
      (.returned (nextSqrt0FinalFrame imms a) evm
        (some [.int (Int.ofNat (nextSqrt0Result a).toNat)])) := by
  rw [← List.take_append_drop 2 (nextSqrt0Branch a.add)]
  apply execBlock_append_ok (nextSqrt0ProductSource imms evm a)
  cases ha : a.add
  · simp only [nextSqrt0Valid, if_neg hn, ha, Bool.false_eq_true, if_false] at hv
    simpa only [nextSqrt0FinalFrame, nextSqrt0Result, nextSqrt0Computed, if_neg hn,
      ha, Bool.false_eq_true, false_and, if_false] using
      nextSqrt0SubtractReturns imms evm a ha hn hv.1 hv.2.1 hv.2.2
  · by_cases hs : nextSqrt0Fast a
    · have hf : nextSqrt0FullValid a := by
        simpa only [nextSqrt0Valid, if_neg hn, ha, if_true, if_pos hs] using hv
      simp only [nextSqrt0FinalFrame, nextSqrt0Result, nextSqrt0Computed, if_neg hn,
        ha, true_and, hs, not_true_eq_false, if_false, if_true]
      exact ExecBlock.consReturn (nextSqrt0FastChoiceReturns imms evm a ha hn hs hf)
    · have hf : nextSqrt0FallbackValid a := by
        simpa only [nextSqrt0Valid, if_neg hn, ha, if_true, if_neg hs] using hv
      simp only [nextSqrt0FinalFrame, nextSqrt0Result, nextSqrt0Computed, if_neg hn,
        ha, true_and, hs, not_false_eq_true, if_false, if_true]
      exact ExecBlock.consNormal (nextSqrt0FallbackChoice imms evm a ha hn hs)
        (nextSqrt0FallbackReturns imms evm a hf)

theorem nextSqrt0BranchReverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hn : a.amount.toNat ≠ 0) (hv : ¬nextSqrt0Valid a) :
    ExecBlock config (nextSqrt0NumeratorFrame imms a) evm (nextSqrt0Branch a.add) .reverted := by
  rw [← List.take_append_drop 2 (nextSqrt0Branch a.add)]
  apply execBlock_append_ok (nextSqrt0ProductSource imms evm a)
  cases ha : a.add
  · apply nextSqrt0SubtractReverts imms evm a ha hn
    simpa only [nextSqrt0Valid, if_neg hn, ha, Bool.false_eq_true, if_false] using hv
  · by_cases hs : nextSqrt0Fast a
    · apply ExecBlock.consRevert (nextSqrt0FastChoiceReverts imms evm a ha hn hs ?_)
      simpa only [nextSqrt0Valid, if_neg hn, ha, if_true, if_pos hs] using hv
    · refine ExecBlock.consNormal (nextSqrt0FallbackChoice imms evm a ha hn hs)
        (ExecBlock.consRevert (nextSqrt0FallbackAddReverts imms evm a ?_))
      simpa only [nextSqrt0Valid, if_neg hn, ha, if_true, if_neg hs] using hv

theorem nextSqrt0Returns (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : nextSqrt0Valid a) :
    ExecFuncBody config (nextSqrtFrame imms a) evm (nextSqrtFunction false).body
      (.returned (nextSqrt0FinalFrame imms a) evm
        (some [.int (Int.ofNat (nextSqrt0Result a).toNat)])) := by
  by_cases hn : a.amount.toNat = 0
  · simpa only [nextSqrt0FinalFrame, nextSqrt0Result, if_pos hn]
      using nextSqrt0ZeroReturns imms evm a hn
  · apply ExecFuncBody.execBlockRet
    rw [← List.take_append_drop 2 (nextSqrtFunction false).body]
    apply execBlock_append_ok (nextSqrt0NumeratorSource imms evm a hn)
    apply ExecBlock.consReturn
    have he : evalExpr? config (nextSqrt0NumeratorFrame imms a) evm (.var "add") =
        .ok (.bool a.add) := evalExpr_var_get (by
      simpa only [nextSqrt0NumeratorFrame, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using (nextSqrtGet imms a).2.2.2)
    have hb := nextSqrt0BranchReturns imms evm a hn hv
    cases ha : a.add
    · exact ExecStmt.iteFalse (by simpa only [ha] using he) (by simpa only [ha] using hb)
    · exact ExecStmt.iteTrue (by simpa only [ha] using he) (by simpa only [ha] using hb)

theorem nextSqrt0Reverts (imms : Store) (evm : EVM.State) (a : NextSqrtArgs)
    (hv : ¬nextSqrt0Valid a) :
    ExecFuncBody config (nextSqrtFrame imms a) evm (nextSqrtFunction false).body .reverted := by
  have hn : a.amount.toNat ≠ 0 := fun h ↦ hv (by simp only [nextSqrt0Valid, if_pos h])
  apply ExecFuncBody.execBlockRevert
  rw [← List.take_append_drop 2 (nextSqrtFunction false).body]
  apply execBlock_append_ok (nextSqrt0NumeratorSource imms evm a hn)
  apply ExecBlock.consRevert
  have he : evalExpr? config (nextSqrt0NumeratorFrame imms a) evm (.var "add") =
      .ok (.bool a.add) := evalExpr_var_get (by
    simpa only [nextSqrt0NumeratorFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] using (nextSqrtGet imms a).2.2.2)
  have hb := nextSqrt0BranchReverts imms evm a hn hv
  cases ha : a.add
  · exact ExecStmt.iteFalse (by simpa only [ha] using he) (by simpa only [ha] using hb)
  · exact ExecStmt.iteTrue (by simpa only [ha] using he) (by simpa only [ha] using hb)

end Benchmarks.UniswapV3.Pool
