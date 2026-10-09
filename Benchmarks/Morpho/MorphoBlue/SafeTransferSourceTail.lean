import Benchmarks.Morpho.MorphoBlue.SafeTransferSourceAllocation

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

theorem safeTransferTail_ready {frame : Frame} {evm : EVM.State} {n : Nat}
    {out : ByteArray} {success : Bool}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool success))
    (hb : out.size < 2 ^ 64) (hc : n + safeTransferReturnAlloc out.size + 128 < 2 ^ 64) :
    ∃ frame', ABlock config evm frame safeTransferTail frame' (safeTransferTail.drop 3) ∧
      frame'.locals.get? "__memory" =
        some (.int (Int.ofNat (n + safeTransferReturnAlloc out.size + 128))) ∧
      frame'.locals.get? "returndata" = some (.bytes out) ∧
      frame'.locals.get? "success" = some (.bool success) := by
  obtain ⟨frame', hp, hm', hother⟩ := safeTransferTail_allocationPrefix_preserves hm hout hb
  have he : evalExpr? config frame' evm (.var "__memory") =
      .ok (.int (Int.ofNat (n + safeTransferReturnAlloc out.size + 128))) := by
    simp only [evalExpr?, hm', EvalResult.ofOption]
  refine ⟨frame', hp.requireStep ?_, hm', (hother "returndata" (by decide)).trans hout,
    (hother "success" (by decide)).trans hz⟩
  exact (safeTransferCap_eval he).trans (by rw [decide_eq_true (by omega)])

theorem safeTransferTail_callFailure {frame : Frame} {evm : EVM.State} {n : Nat}
    {out : ByteArray}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool false)) :
    ExecBlock config frame evm safeTransferTail .reverted := by
  by_cases hb : out.size < 2 ^ 64
  · by_cases hc : n + safeTransferReturnAlloc out.size + 128 < 2 ^ 64
    · obtain ⟨frame', hp, _, _, hz'⟩ := safeTransferTail_ready hm hout hz hb hc
      apply hp.run (ExecBlock.consRevert (.requireFalse ?_))
      simp only [evalExpr?, hz', EvalResult.ofOption]
    · exact safeTransferTail_allocationRevert hm hout hb (by omega)
  · exact safeTransferTail_oversize hout (by omega)

theorem safeTransferTail_decodeFailure {frame : Frame} {evm : EVM.State} {n : Nat}
    {out : ByteArray}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool true)) (hn : out.size ≠ 0)
    (hd : ABI.decodeReturnValueWithMode? config.abiDecodeMode abiBool out = none ∨
      ABI.decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool false)) :
    ExecBlock config frame evm safeTransferTail .reverted := by
  by_cases hb : out.size < 2 ^ 64
  · by_cases hc : n + safeTransferReturnAlloc out.size + 128 < 2 ^ 64
    · obtain ⟨frame', hp, _, hout', hz'⟩ := safeTransferTail_ready hm hout hz hb hc
      have he : evalExpr? config frame' evm (.var "success") = .ok (.bool true) := by
        simp only [evalExpr?, hz', EvalResult.ofOption]
      apply (hp.requireStep he).run
      apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
      · exact (safeTransferHasReturn_eval hout').trans (by rw [decide_eq_true hn])
      · rcases hd with hd | hd
        · apply ExecBlock.consRevert (ExecStmt.requireRevert ?_)
          simp only [evalExpr?, hout', EvalResult.ofOption, pure, bind, EvalResult.bind, hd]
        · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
          simp only [evalExpr?, hout', EvalResult.ofOption, pure, bind, EvalResult.bind, hd]
    · exact safeTransferTail_allocationRevert hm hout hb (by omega)
  · exact safeTransferTail_oversize hout (by omega)

theorem safeTransferTail_success {frame : Frame} {evm : EVM.State} {n : Nat}
    {out : ByteArray}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out))
    (hz : frame.locals.get? "success" = some (.bool true))
    (hb : out.size < 2 ^ 64) (hc : n + safeTransferReturnAlloc out.size + 128 < 2 ^ 64)
    (hd : out.size = 0 ∨
      ABI.decodeReturnValueWithMode? config.abiDecodeMode abiBool out = some (.bool true)) :
    ∃ frame', ExecBlock config frame evm safeTransferTail
      (.returned frame' evm (some [.int (Int.ofNat (n + safeTransferReturnAlloc out.size + 128))])) := by
  obtain ⟨frame', hp, hm', hout', hz'⟩ := safeTransferTail_ready hm hout hz hb hc
  have he : evalExpr? config frame' evm (.var "success") = .ok (.bool true) := by
    simp only [evalExpr?, hz', EvalResult.ofOption]
  have hif : ExecStmt config frame' evm safeTransferTail[4]! (.ok frame' evm) := by
    by_cases hn : out.size = 0
    · apply ExecStmt.iteFalse ?_ ExecBlock.nil
      exact (safeTransferHasReturn_eval hout').trans (by rw [decide_eq_false (not_not.mpr hn)])
    · have hd := hd.resolve_left hn
      apply ExecStmt.iteTrue ?_ (ExecBlock.consNormal (ExecStmt.requireTrue ?_) ExecBlock.nil)
      · exact (safeTransferHasReturn_eval hout').trans (by rw [decide_eq_true hn])
      · simp only [evalExpr?, hout', EvalResult.ofOption, pure, bind, EvalResult.bind, hd]
  refine ⟨frame', (hp.requireStep he).run (.consNormal hif (.consReturn (.return ?_)))⟩
  simp only [evalExprs?, evalExpr?, hm', EvalResult.ofOption, pure, bind, EvalResult.bind]

end Benchmarks.Morpho.MorphoBlue
