import Benchmarks.UniswapV3.Pool.BitScanBounds

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def bitMsbStepStmt (bits : Nat) (shift : Bool) : Stmt :=
  .ite (.binary .ge (.var "x") (.intLit (Int.ofNat (2 ^ bits))))
    ((if shift then [.assign .localVar ⟨"x", []⟩
      (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "x") (.intLit (Int.ofNat bits)))]
      else []) ++
      [.assign .localVar ⟨"r", []⟩ (.cast (.binary .add (.var "r") (.intLit (Int.ofNat bits)))
        (.elem (.int (.uint ⟨8, by decide⟩))))]) []

theorem bitMsbStepSource {frame : Frame} {evm : EVM.State}
    (state : Nat × UInt256) (bits : Nat) (shift : Bool)
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat state.1)))
    (hx : frame.locals.get? "x" = some (.int (Int.ofNat state.2.toNat)))
    (hb : state.1 + bits < 256) :
    ∃ frame', ExecStmt config frame evm (bitMsbStepStmt bits shift) (.ok frame' evm) ∧
      frame'.locals.get? "r" = some (.int (Int.ofNat (tickLogMsbStep state bits).1)) ∧
      frame'.locals.get? "x" = some (.int (Int.ofNat
        (if shift then (tickLogMsbStep state bits).2 else state.2).toNat)) := by
  have he := evalExpr_var_get (cfg := config) (evm := evm) hx
  have hg : evalExpr? config frame evm
      (.binary .ge (.var "x") (.intLit (Int.ofNat (2 ^ bits)))) =
      .ok (.bool (decide (2 ^ bits ≤ state.2.toNat))) := by
    simp only [evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure]
    congr 2
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    exact Int.ofNat_le
  by_cases h : 2 ^ bits ≤ state.2.toNat
  · let mid : Frame := if shift then
      {frame with
        locals := frame.locals.insert "x"
          (.int (Int.ofNat (UInt256.shiftRight state.2 (UInt256.ofNat bits)).toNat))}
      else frame
    have hm : ExecBlock config frame evm
        (if shift then [.assign .localVar ⟨"x", []⟩
          (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "x") (.intLit (Int.ofNat bits)))]
          else []) (.ok mid evm) := by
      cases shift
      · exact ExecBlock.nil
      · exact ExecBlock.consNormal
          (ExecStmt.assign (evalExpr_word_shr bits (by omega) he)
            (assignLocalVarBase_frame hx)) ExecBlock.nil
    have hr' : mid.locals.get? "r" = some (.int (Int.ofNat state.1)) := by
      cases shift <;> simpa [mid, Std.HashMap.getElem?_insert] using hr
    let out : Frame := {mid with locals := mid.locals.insert "r" (.int (Int.ofNat (state.1 + bits)))}
    refine ⟨out, ExecStmt.iteTrue (by simpa only [h, decide_true] using hg) ?_, ?_, ?_⟩
    · apply execBlock_append_ok hm
      refine ExecBlock.consNormal (ExecStmt.assign (value := .int (Int.ofNat (state.1 + bits)))
        ?_ (assignLocalVarBase_frame hr')) ExecBlock.nil
      have er := evalExpr_var_get (cfg := config) (evm := evm) hr'
      simp only [evalExpr?, er, evalBinaryOp?, castValue?, bind, EvalResult.bind, pure]
      change EvalResult.ok (Value.int (normalizeInt (.uint ⟨8, by decide⟩)
        (Int.ofNat (state.1 + bits)))) = .ok (Value.int (Int.ofNat (state.1 + bits)))
      rw [normalizeInt_uint_eq_self ⟨8, by decide⟩ (Int.ofNat (state.1 + bits))
        (Int.natCast_nonneg _) (Int.ofNat_lt.mpr hb)]
    · simp only [out, tickLogMsbStep, if_pos h, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert_self]
    · cases shift
      · simpa only [out, mid, Bool.false_eq_true, ↓reduceIte,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          show ("r" == "x") = false from rfl] using hx
      · simp only [out, mid, ↓reduceIte, tickLogMsbStep, if_pos h,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          show ("r" == "x") = false from rfl, show ("x" == "x") = true from rfl,
          Bool.false_eq_true, ↓reduceIte]
  · refine ⟨frame, ExecStmt.iteFalse (by simpa only [h, decide_false] using hg)
      ExecBlock.nil, ?_, ?_⟩
    · simpa only [tickLogMsbStep, if_neg h] using hr
    · cases shift <;> simpa only [tickLogMsbStep, if_neg h, Bool.false_eq_true,
        ↓reduceIte] using hx

theorem bitMsbFoldSource {frame : Frame} {evm : EVM.State}
    (state : Nat × UInt256) (bits : List Nat)
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat state.1)))
    (hx : frame.locals.get? "x" = some (.int (Int.ofNat state.2.toNat)))
    (hb : state.1 + bits.sum < 256) :
    ∃ frame', ExecBlock config frame evm (bits.map (fun b ↦ bitMsbStepStmt b true))
        (.ok frame' evm) ∧
      frame'.locals.get? "r" = some (.int (Int.ofNat (bits.foldl tickLogMsbStep state).1)) ∧
      frame'.locals.get? "x" = some (.int (Int.ofNat (bits.foldl tickLogMsbStep state).2.toNat)) := by
  induction bits generalizing frame state with
  | nil => exact ⟨frame, ExecBlock.nil, hr, hx⟩
  | cons b bs ih =>
    have hs := tickLogMsbStep_count_le state b
    simp only [List.sum_cons] at hb
    obtain ⟨mid, hm, hr', hx'⟩ := bitMsbStepSource (evm := evm) state b true hr hx (by omega)
    obtain ⟨out, ho, hr'', hx''⟩ := ih (tickLogMsbStep state b) hr' hx' (by omega)
    exact ⟨out, ExecBlock.consNormal hm ho, hr'', hx''⟩

end Benchmarks.UniswapV3.Pool
