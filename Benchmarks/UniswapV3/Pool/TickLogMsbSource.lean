import Benchmarks.UniswapV3.Pool.TickLogPrefix

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def tickLogMsbBits : List Nat := [128, 64, 32, 16, 8, 4, 2, 1]

def tickLogMsbStep (state : Nat × UInt256) (bits : Nat) : Nat × UInt256 :=
  if 2 ^ bits ≤ state.2.toNat then
    (state.1 + bits, UInt256.shiftRight state.2 (UInt256.ofNat bits))
  else state

def tickLogMsb (price : UInt256) : Nat × UInt256 :=
  tickLogMsbBits.foldl tickLogMsbStep (0, tickLogRatio price)

def tickLogMsbGuard (bits : Nat) : Expr :=
  .binary .ge (.var "r") (.binary .exp (.intLit 2) (.intLit (Int.ofNat bits)))

def tickLogMsbStmt (bits : Nat) : Stmt :=
  .ite (tickLogMsbGuard bits)
    [.assign .localVar ⟨"msb", []⟩ (.binary .add (.var "msb") (.intLit (Int.ofNat bits))),
     .assign .localVar ⟨"r", []⟩
       (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "r") (.intLit (Int.ofNat bits)))] []

theorem evalTickLogMsbGuard {frame : Frame} {evm : EVM.State} (r : UInt256) (bits : Nat)
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat r.toNat))) :
    evalExpr? config frame evm (tickLogMsbGuard bits) =
      .ok (.bool (decide (2 ^ bits ≤ r.toNat))) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hr
  simp only [tickLogMsbGuard, evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure,
    show ¬ Int.ofNat bits < 0 from Int.not_lt.mpr (Int.natCast_nonneg _), ↓reduceIte]
  change EvalResult.ok (Value.bool (decide ((2 : Int) ^ bits ≤ Int.ofNat r.toNat))) = _
  rw [show (2 : Int) ^ bits = Int.ofNat (2 ^ bits) by simp]
  apply congrArg (fun b ↦ EvalResult.ok (Value.bool b))
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  exact Int.ofNat_le

theorem tickLogMsbStepSource {frame : Frame} {evm : EVM.State}
    (state : Nat × UInt256) (bits : Nat)
    (hm : frame.locals.get? "msb" = some (.int (Int.ofNat state.1)))
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat state.2.toNat)))
    (hb : bits < 256) :
    ∃ frame', ExecStmt config frame evm (tickLogMsbStmt bits) (.ok frame' evm) ∧
      frame'.locals.get? "msb" = some (.int (Int.ofNat (tickLogMsbStep state bits).1)) ∧
      frame'.locals.get? "r" = some (.int (Int.ofNat (tickLogMsbStep state bits).2.toNat)) ∧
      (∀ name, name ≠ "msb" → name ≠ "r" →
        frame'.locals.get? name = frame.locals.get? name) := by
  have he := evalTickLogMsbGuard (evm := evm) state.2 bits hr
  by_cases h : 2 ^ bits ≤ state.2.toNat
  · let mid : Frame :=
      {frame with locals := frame.locals.insert "msb" (.int (Int.ofNat (state.1 + bits)))}
    let out : Frame :=
      {mid with
        locals := mid.locals.insert "r"
          (.int (Int.ofNat (UInt256.shiftRight state.2 (UInt256.ofNat bits)).toNat))}
    have hr' : mid.locals.get? "r" = some (.int (Int.ofNat state.2.toNat)) := by
      simpa [mid, Std.HashMap.getElem?_insert] using hr
    refine ⟨out, ?_, ?_, ?_, ?_⟩
    · refine ExecStmt.iteTrue (by simpa only [h, decide_true] using he) ?_
      refine ExecBlock.consNormal (solm' := mid) (evm' := evm)
        (ExecStmt.assign (value := .int (Int.ofNat (state.1 + bits))) ?_ ?_) ?_
      · have hm' := evalExpr_var_get (cfg := config) (evm := evm) hm
        simp only [evalExpr?, hm', evalBinaryOp?, bind, EvalResult.bind, pure]
        rfl
      · exact assignLocalVarBase_frame hm
      refine ExecBlock.consNormal (solm' := out)
        (ExecStmt.assign (value := .int
          (Int.ofNat (UInt256.shiftRight state.2 (UInt256.ofNat bits)).toNat)) ?_ ?_) ExecBlock.nil
      · exact evalExpr_word_shr bits hb (evalExpr_var_get hr')
      · exact assignLocalVarBase_frame hr'
    · simp [out, mid, tickLogMsbStep, h, Std.HashMap.getElem_insert]
    · simp [out, tickLogMsbStep, h]
    · intro name hnm hnr
      simp [out, mid, Std.HashMap.getElem?_insert, Ne.symm hnm, Ne.symm hnr]
  · refine ⟨frame, ExecStmt.iteFalse ?_ ExecBlock.nil, ?_, ?_, fun _ _ _ ↦ rfl⟩
    · simpa only [h, decide_false] using he
    · simpa only [tickLogMsbStep, if_neg h] using hm
    · simpa only [tickLogMsbStep, if_neg h] using hr

theorem tickLogMsbFoldSource {frame : Frame} {evm : EVM.State}
    (state : Nat × UInt256) (bits : List Nat)
    (hm : frame.locals.get? "msb" = some (.int (Int.ofNat state.1)))
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat state.2.toNat)))
    (hb : ∀ b ∈ bits, b < 256) :
    ∃ frame', ExecBlock config frame evm (bits.map tickLogMsbStmt) (.ok frame' evm) ∧
      frame'.locals.get? "msb" = some (.int (Int.ofNat (bits.foldl tickLogMsbStep state).1)) ∧
      frame'.locals.get? "r" = some (.int (Int.ofNat (bits.foldl tickLogMsbStep state).2.toNat)) ∧
      (∀ name, name ≠ "msb" → name ≠ "r" →
        frame'.locals.get? name = frame.locals.get? name) := by
  induction bits generalizing frame state with
  | nil => exact ⟨frame, ExecBlock.nil, hm, hr, fun _ _ _ ↦ rfl⟩
  | cons b bs ih =>
    obtain ⟨mid, hs, hm', hr', hp⟩ := tickLogMsbStepSource (evm := evm)
      state b hm hr (hb b (by simp))
    obtain ⟨out, hs', hm'', hr'', hp'⟩ := ih (tickLogMsbStep state b) hm' hr'
      (fun b hmem ↦ hb b (by simp [hmem]))
    exact ⟨out, ExecBlock.consNormal hs hs', hm'', hr'',
      fun name hnm hnr ↦ (hp' name hnm hnr).trans (hp name hnm hnr)⟩

theorem tickLogMsbSource (imms : Store) (evm : EVM.State) (price : UInt256)
    (hp : price.toNat < 2 ^ 160) (hv : tickLogValid price) :
    ∃ frame, ExecBlock config (tickLogFrame imms price) evm (tickLogFunction.body.take 13)
        (.ok frame evm) ∧
      frame.locals.get? "msb" = some (.int (Int.ofNat (tickLogMsb price).1)) ∧
      frame.locals.get? "r" = some (.int (Int.ofNat (tickLogMsb price).2.toNat)) ∧
      frame.locals.get? "ratio" = some (.int (Int.ofNat (tickLogRatio price).toNat)) ∧
      frame.locals.get? "sqrtPriceX96" = some (.int (Int.ofNat price.toNat)) ∧
      frame.locals.get? "tick" = some (.int 0) := by
  obtain ⟨frame, hs, hm, hr, hpres⟩ := tickLogMsbFoldSource (evm := evm)
    (frame := tickLogReadyFrame imms price) (0, tickLogRatio price) tickLogMsbBits
    (by
      change (tickLogReadyFrame imms price).locals["msb"]? = _
      exact Std.HashMap.getElem?_insert_self)
    (by
      change (tickLogReadyFrame imms price).locals["r"]? = _
      simp only [tickLogReadyFrame, Std.HashMap.getElem?_insert, show ("msb" == "r") = false from rfl,
        show ("r" == "r") = true from rfl, Bool.false_eq_true, ↓reduceIte]) (by decide)
  refine ⟨frame, ?_, hm, hr, ?_, ?_, ?_⟩
  · change ExecBlock _ _ _ (tickLogFunction.body.take 5 ++
      tickLogMsbBits.map tickLogMsbStmt) _
    exact execBlock_append_ok (tickLogReadySource imms evm price hp hv) hs
  · rw [hpres "ratio" (by decide) (by decide)]
    change (tickLogReadyFrame imms price).locals["ratio"]? = _
    simp only [tickLogReadyFrame, tickLogRatioFrame, Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]
    rfl
  · rw [hpres "sqrtPriceX96" (by decide) (by decide)]
    change (tickLogReadyFrame imms price).locals["sqrtPriceX96"]? = _
    simp only [tickLogReadyFrame, tickLogRatioFrame, tickLogZeroFrame, tickLogFrame,
      tickLogLocals, Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]
    rfl
  · rw [hpres "tick" (by decide) (by decide)]
    change (tickLogReadyFrame imms price).locals["tick"]? = _
    simp only [tickLogReadyFrame, tickLogRatioFrame, tickLogZeroFrame, Std.HashMap.getElem?_insert, beq_self_eq_true, ↓reduceIte]
    rfl

end Benchmarks.UniswapV3.Pool
