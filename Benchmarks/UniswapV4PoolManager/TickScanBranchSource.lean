import Benchmarks.UniswapV4PoolManager.TickScanPreludeSource
import Benchmarks.UniswapV4PoolManager.TickScanInitializedSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem tickScanTailSource {f : Frame} {evm : EVM.State} {compressed spacing masked : UInt256}
    (lte : Bool) (hf : f.contract = contract)
    (hc : f.locals.get? "compressed" = some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))))
    (hs : f.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)))
    (hb : f.locals.get? "bitPos" = some (.int (Int.ofNat (tickPositionBit compressed).toNat)))
    (hm : f.locals.get? "masked" = some (.int (Int.ofNat masked.toNat)))
    (hi : f.locals.get? "initialized" = some (.bool (decide (masked ≠ ⟨0⟩)))) :
    ∃ f', ExecBlock config f evm (tickScanTailStmts lte)
      (.returned f' evm (some (tickScanResultValues compressed spacing masked lte))) := by
  let next := tickScanNextWord compressed spacing (tickScanDefaultDistance (tickPositionBit compressed) lte) lte
  let f1 := valueLocal f "next" (.int (EVM.signed next))
  have hnext : ExecStmt config f evm (tickScanTailStmts lte)[0]! (.ok f1 evm) :=
    ExecStmt.letDecl (tickScanNext_eval lte hc hs
      (tickScanDefaultDistance_fits (tickPositionBit_fits compressed) lte)
      (tickScanDefault_eval lte hb))
  have hc1 : f1.locals.get? "compressed" = some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))) :=
    (store_get_ne _ _ (by decide : ("next" == "compressed") = false)).trans hc
  have hs1 : f1.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)) :=
    (store_get_ne _ _ (by decide : ("next" == "tickSpacing") = false)).trans hs
  have hb1 : f1.locals.get? "bitPos" = some (.int (Int.ofNat (tickPositionBit compressed).toNat)) :=
    (store_get_ne _ _ (by decide : ("next" == "bitPos") = false)).trans hb
  have hm1 : f1.locals.get? "masked" = some (.int (Int.ofNat masked.toNat)) :=
    (store_get_ne _ _ (by decide : ("next" == "masked") = false)).trans hm
  have hi1 : f1.locals.get? "initialized" = some (.bool (decide (masked ≠ ⟨0⟩))) :=
    (store_get_ne _ _ (by decide : ("next" == "initialized") = false)).trans hi
  have hn1 : f1.locals.get? "next" = some (.int (EVM.signed next)) := store_get_self _ _ _
  by_cases hz : masked = ⟨0⟩
  · refine ⟨f1, ExecBlock.consNormal hnext (ExecBlock.consNormal
      (ExecStmt.iteFalse ?_ ExecBlock.nil) (ExecBlock.consReturn (ExecStmt.return ?_)))⟩
    · simpa only [hz, ne_eq, not_true_eq_false, decide_false] using evalLocalValue (cfg := config) (evm := evm) hi1
    · simp only [evalExprs?, evalLocalValue hn1, evalLocalValue hi1, bind, EvalResult.bind, pure,
        tickScanResultValues, tickScanResultWord, if_pos hz]
      rfl
  · let f2 := tickScanInitializedFrame f1 compressed spacing masked lte
    have hinit := tickScanInitializedSource lte (f := f1) (evm := evm)
      ((valueLocal_contract f "next" (.int (EVM.signed next))).trans hf) hc1 hs1 hb1 hm1 hn1 hz
    have hn2 : f2.locals.get? "next" = some (.int (EVM.signed (tickScanNextWord compressed spacing
        (tickScanDistance (tickPositionBit compressed) (tickScanIndex masked lte) lte) lte))) := store_get_self _ _ _
    have hi2 : f2.locals.get? "initialized" = some (.bool (decide (masked ≠ ⟨0⟩))) :=
      (store_get_ne _ _ (by decide : ("next" == "initialized") = false)).trans
        ((tickScanIndexFrame_get f1 masked lte "initialized" (by decide) (by decide)).trans hi1)
    refine ⟨f2, ExecBlock.consNormal hnext (ExecBlock.consNormal
      (ExecStmt.iteTrue ?_ hinit) (ExecBlock.consReturn (ExecStmt.return ?_)))⟩
    · simpa only [decide_eq_true hz] using evalLocalValue (cfg := config) (evm := evm) hi1
    · change evalExprs? config f2 evm [.var "next", .var "initialized"] = _
      simp only [evalExprs?, evalLocalValue hn2, evalLocalValue hi2, bind, EvalResult.bind, pure,
        tickScanResultValues, tickScanResultWord, if_neg hz]

theorem tickScanBranchSource {f : Frame} {evm : EVM.State} {id compressed spacing : UInt256}
    (lte : Bool) (hf : f.contract = contract)
    (hc : f.locals.get? "compressed" = some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))))
    (hs : f.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)))
    (href : f.locals.get? "self" = some (tickBitmapRefValue id)) :
    ∃ f', ExecBlock config f evm (tickScanBranchStmts lte)
      (.returned f' evm (some (tickScanResultValues compressed spacing (tickScanMasked evm id compressed lte) lte))) := by
  let f0 := tickScanPreludeFrame f evm id compressed lte
  have hpre := tickScanPreludeSource (evm := evm) lte hf hc href
  have hf0 : f0.contract = contract := (tickScanPreludeFrame_contract f evm id compressed lte).trans hf
  have hc0 : f0.locals.get? "compressed" = some (.int (EVM.signed (UInt256.signextend (UInt256.ofNat 2) compressed))) := by
    simp only [f0, tickScanPreludeFrame_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hc]
  have hs0 : f0.locals.get? "tickSpacing" = some (.int (EVM.signed spacing)) := by
    simp only [f0, tickScanPreludeFrame_get, beq_iff_eq, String.reduceEq, ↓reduceIte, hs]
  have hb0 : f0.locals.get? "bitPos" = some (.int (Int.ofNat (tickPositionBit compressed).toNat)) := by
    simp only [f0, tickScanPreludeFrame_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hm0 : f0.locals.get? "masked" = some (.int (Int.ofNat (tickScanMasked evm id compressed lte).toNat)) := by
    simp only [f0, tickScanPreludeFrame_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  have hi0 : f0.locals.get? "initialized" = some (.bool (decide (tickScanMasked evm id compressed lte ≠ ⟨0⟩))) := by
    simp only [f0, tickScanPreludeFrame_get, beq_iff_eq, String.reduceEq, ↓reduceIte]
  obtain ⟨f', htail⟩ := tickScanTailSource (evm := evm) lte hf0 hc0 hs0 hb0 hm0 hi0
  exact ⟨f', execBlock_append_ok hpre htail⟩

end Benchmarks.UniswapV4PoolManager
