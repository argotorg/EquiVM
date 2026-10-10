import Benchmarks.UniswapV3.Pool.BitmapNextComputeSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

def bitmapNextReadyFrame (imms : Store) (evm : EVM.State)
    (tick spacing : Int) (lte : Bool) : Frame :=
  let compressed := bitmapNextCompressed tick spacing
  let masked := bitmapNextMasked evm compressed lte
  let computed := bitmapNextComputedFrame imms
    (bitmapNextCondFrame imms evm tick spacing lte).locals compressed spacing lte masked
  {computed with
    locals := computed.locals.insert "next" (.int (bitmapNextResult compressed spacing lte masked))}

theorem bitmapNextCondGet (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool) :
    let frame := bitmapNextCondFrame imms evm tick spacing lte
    let compressed := bitmapNextCompressed tick spacing
    let masked := bitmapNextMasked evm compressed lte
    frame.locals.get? "compressed" = some (.int compressed) ∧
      frame.locals.get? "tickSpacing" = some (.int spacing) ∧
      frame.locals.get? "bitPos" = some (.int (bitmapBitPos (bitmapNextPosition compressed lte))) ∧
      frame.locals.get? "masked" = some (.int (Int.ofNat masked.toNat)) ∧
      frame.locals.get? "initialized" = some (.bool (decide (masked ≠ ⟨0⟩))) ∧
      frame.locals.get? (bitmapNextCondName lte) = some (.int 0) ∧
      frame.locals.get? "next" = some (.int 0) := by
  dsimp only
  have hp := bitmapNextPrefixGet imms tick spacing lte
  cases lte <;>
    simp only [bitmapNextCondFrame, bitmapNextInitFrame, bitmapNextReadFrame, bitmapNextMaskFrame,
      bitmapNextBitFrame, bitmapNextWordFrame, bitmapNextCallFrame, bitmapNextCondName,
      bitmapNextCallName, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] <;>
    exact ⟨hp.1, hp.2.1, rfl, rfl, rfl, rfl, hp.2.2.2.1⟩

theorem bitmapNextComputedGet (imms locals : Store) (compressed spacing : Int)
    (lte : Bool) (masked : UInt256) :
    let frame := bitmapNextComputedFrame imms locals compressed spacing lte masked
    frame.locals.get? (bitmapNextCondName lte) =
        some (.int (bitmapNextResult compressed spacing lte masked)) ∧
      frame.locals.get? "next" = locals.get? "next" ∧
      frame.locals.get? "initialized" = locals.get? "initialized" := by
  dsimp only
  cases lte <;> by_cases hz : masked = ⟨0⟩ <;>
    simp only [bitmapNextComputedFrame, bitmapNextScanFrame, bitmapNextCondName,
      bitmapNextScanName, hz, ↓reduceIte, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert] <;> exact ⟨rfl, rfl, rfl⟩

theorem bitmapNextBranchSource (imms : Store) (evm : EVM.State)
    (tick spacing : Int) (lte : Bool) :
    ExecBlock config (bitmapNextPrefixFrame imms tick spacing lte) evm (bitmapNextBranch lte)
      (.ok (bitmapNextReadyFrame imms evm tick spacing lte) evm) := by
  rw [← List.take_append_drop 3 (bitmapNextBranch lte)]
  apply execBlock_append_ok (bitmapNextPositionSource imms evm tick spacing lte)
  rw [← List.take_append_drop 4 ((bitmapNextBranch lte).drop 3)]
  apply execBlock_append_ok (bitmapNextReadSource imms evm tick spacing lte)
  simp only [List.drop_drop]
  obtain ⟨hc, hs, hb, hm, hi, hh, hn⟩ := bitmapNextCondGet imms evm tick spacing lte
  let locals := (bitmapNextCondFrame imms evm tick spacing lte).locals
  let compressed := bitmapNextCompressed tick spacing
  let masked := bitmapNextMasked evm compressed lte
  have hcompute := bitmapNextComputeSource imms locals evm compressed spacing lte masked
    hc hs hb hm hi hh
  obtain ⟨hcond, hnext, _⟩ := bitmapNextComputedGet imms locals compressed spacing lte masked
  have ha : ExecStmt config (bitmapNextComputedFrame imms locals compressed spacing lte masked) evm
      (.assign .localVar ⟨"next", []⟩ (.var (bitmapNextCondName lte)))
      (.ok (bitmapNextReadyFrame imms evm tick spacing lte) evm) :=
    ExecStmt.assign (evalExpr_var_get hcond) (assignLocalVarBase_frame (hnext.trans hn))
  cases lte <;> exact ExecBlock.consNormal hcompute (ExecBlock.consNormal ha ExecBlock.nil)

theorem bitmapNextReadyGet (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool) :
    let compressed := bitmapNextCompressed tick spacing
    let masked := bitmapNextMasked evm compressed lte
    (bitmapNextReadyFrame imms evm tick spacing lte).locals.get? "next" =
        some (.int (bitmapNextResult compressed spacing lte masked)) ∧
      (bitmapNextReadyFrame imms evm tick spacing lte).locals.get? "initialized" =
        some (.bool (decide (masked ≠ ⟨0⟩))) := by
  dsimp only
  have hi := (bitmapNextComputedGet imms (bitmapNextCondFrame imms evm tick spacing lte).locals
    (bitmapNextCompressed tick spacing) spacing lte
    (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte)).2.2
  have hg := (bitmapNextCondGet imms evm tick spacing lte).2.2.2.2.1
  simp only [bitmapNextReadyFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
  exact ⟨rfl, hi.trans hg⟩

theorem bitmapNextReturns (imms : Store) (evm : EVM.State) (tick spacing : Int) (lte : Bool)
    (hn : spacing ≠ 0) :
    let compressed := bitmapNextCompressed tick spacing
    let masked := bitmapNextMasked evm compressed lte
    ExecFuncBody config (bitmapNextFrame imms tick spacing lte) evm bitmapNextFunction.body
      (.returned (bitmapNextReadyFrame imms evm tick spacing lte) evm
        (some [.int (bitmapNextResult compressed spacing lte masked),
          .bool (decide (masked ≠ ⟨0⟩))])) := by
  dsimp only
  apply ExecFuncBody.execBlockRet
  rw [← List.take_append_drop 4 bitmapNextFunction.body]
  apply execBlock_append_ok (bitmapNextPrefixSource imms evm tick spacing lte hn)
  have hbranch := bitmapNextBranchSource imms evm tick spacing lte
  have he := evalExpr_var_get (cfg := config) (evm := evm)
    (bitmapNextPrefixGet imms tick spacing lte).2.2.1
  have hnxt := evalExpr_var_get (cfg := config) (evm := evm)
    (bitmapNextReadyGet imms evm tick spacing lte).1
  have hini := evalExpr_var_get (cfg := config) (evm := evm)
    (bitmapNextReadyGet imms evm tick spacing lte).2
  have hr : ExecStmt config (bitmapNextReadyFrame imms evm tick spacing lte) evm
      (.return [(.var "next"), (.var "initialized")])
      (.returned (bitmapNextReadyFrame imms evm tick spacing lte) evm
        (some [.int (bitmapNextResult (bitmapNextCompressed tick spacing) spacing lte
          (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte)),
          .bool (decide (bitmapNextMasked evm (bitmapNextCompressed tick spacing) lte ≠ ⟨0⟩))])) :=
    ExecStmt.return (by simp only [evalExprs?, hnxt, hini, bind, EvalResult.bind, pure])
  cases lte
  · exact ExecBlock.consNormal (ExecStmt.iteFalse he hbranch) (ExecBlock.consReturn hr)
  · exact ExecBlock.consNormal (ExecStmt.iteTrue he hbranch) (ExecBlock.consReturn hr)

end Benchmarks.UniswapV3.Pool
