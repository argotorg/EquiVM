import Benchmarks.UniswapV3.Pool.BitLsbModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def bitLsbGuard (bits : Nat) : Expr :=
  .binary .gt (.binary (.bitAnd (.uint ⟨256, by decide⟩)) (.var "x")
    (.intLit (Int.ofNat (2 ^ bits - 1)))) (.intLit 0)

def bitLsbStepStmt (bits : Nat) (shift : Bool) : Stmt :=
  .ite (bitLsbGuard bits)
    [.assign .localVar ⟨"r", []⟩ (.cast (.binary .sub (.var "r") (.intLit (Int.ofNat bits)))
      (.elem (.int (.uint ⟨8, by decide⟩))))]
    (if shift then [.assign .localVar ⟨"x", []⟩
      (.binary (.shr (.uint ⟨256, by decide⟩)) (.var "x") (.intLit (Int.ofNat bits)))] else [])

theorem evalBitLsbGuard {frame : Frame} {evm : EVM.State} (x : UInt256) (bits : Nat)
    (hx : frame.locals.get? "x" = some (.int (Int.ofNat x.toNat))) (hb : bits < 256) :
    evalExpr? config frame evm (bitLsbGuard bits) =
      .ok (.bool (decide (0 < (bitLsbLow x bits).toNat))) := by
  have hm : (bitLsbMask bits).toNat = 2 ^ bits - 1 :=
    UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.pow_lt_pow_right (by decide) hb))
  apply evalExpr_word_gt (b := ⟨0⟩)
  · apply evalExpr_word_land (evalExpr_var_get hx)
    simp only [evalExpr?, pure, hm]
  · simp only [evalExpr?, pure]
    rfl

theorem bitLsbStepSource {frame : Frame} {evm : EVM.State}
    (state : Nat × UInt256) (bits : Nat) (shift : Bool)
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat state.1)))
    (hx : frame.locals.get? "x" = some (.int (Int.ofNat state.2.toNat)))
    (hb : state.1 < 256) (hle : bits ≤ state.1) :
    ∃ out, ExecStmt config frame evm (bitLsbStepStmt bits shift) (.ok out evm) ∧
      out.locals.get? "r" = some (.int (Int.ofNat (bitLsbStep state bits).1)) ∧
      out.locals.get? "x" = some (.int (Int.ofNat
        (if shift then (bitLsbStep state bits).2 else state.2).toNat)) := by
  have hg := evalBitLsbGuard (evm := evm) state.2 bits hx (by omega)
  by_cases h : 0 < (bitLsbLow state.2 bits).toNat
  · let out : Frame := {frame with
      locals := frame.locals.insert "r" (.int (Int.ofNat (state.1 - bits)))}
    refine ⟨out, ExecStmt.iteTrue (by simpa only [h, decide_true] using hg) ?_, ?_, ?_⟩
    · refine ExecBlock.consNormal (ExecStmt.assign
        (value := .int (Int.ofNat (state.1 - bits))) ?_ (assignLocalVarBase_frame hr)) ExecBlock.nil
      have er := evalExpr_var_get (cfg := config) (evm := evm) hr
      simp only [evalExpr?, er, evalBinaryOp?, castValue?, bind, EvalResult.bind, pure]
      have hsub : Int.ofNat state.1 - Int.ofNat bits = Int.ofNat (state.1 - bits) :=
        (Int.natCast_sub hle).symm
      rw [hsub, normalizeInt_uint_eq_self ⟨8, by decide⟩ (Int.ofNat (state.1 - bits))
        (Int.natCast_nonneg _) (Int.ofNat_lt.mpr (show state.1 - bits < 256 by omega))]
      rfl
    · simp only [out, bitLsbStep, if_pos h, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert_self]
    · cases shift <;> simpa only [out, bitLsbStep, if_pos h, Bool.false_eq_true,
        ↓reduceIte, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        show ("r" == "x") = false from rfl] using hx
  · cases shift
    · refine ⟨frame, ExecStmt.iteFalse (by simpa only [h, decide_false] using hg)
        ExecBlock.nil, ?_, hx⟩
      simpa only [bitLsbStep, if_neg h] using hr
    · let out : Frame := {frame with
        locals := frame.locals.insert "x"
          (.int (Int.ofNat (UInt256.shiftRight state.2 (UInt256.ofNat bits)).toNat))}
      refine ⟨out, ExecStmt.iteFalse (by simpa only [h, decide_false] using hg) ?_, ?_, ?_⟩
      · exact ExecBlock.consNormal (ExecStmt.assign
          (evalExpr_word_shr bits (by omega) (evalExpr_var_get hx))
          (assignLocalVarBase_frame hx)) ExecBlock.nil
      · simpa only [out, bitLsbStep, if_neg h, Std.HashMap.get?_eq_getElem?,
          Std.HashMap.getElem?_insert, show ("x" == "r") = false from rfl,
          Bool.false_eq_true, ↓reduceIte] using hr
      · simp only [out, bitLsbStep, if_neg h, ↓reduceIte,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert_self]

theorem bitLsbFoldSource {frame : Frame} {evm : EVM.State}
    (state : Nat × UInt256) (bits : List Nat)
    (hr : frame.locals.get? "r" = some (.int (Int.ofNat state.1)))
    (hx : frame.locals.get? "x" = some (.int (Int.ofNat state.2.toNat)))
    (hb : state.1 < 256) (hle : bits.sum ≤ state.1) :
    ∃ out, ExecBlock config frame evm (bits.map (fun b ↦ bitLsbStepStmt b true)) (.ok out evm) ∧
      out.locals.get? "r" = some (.int (Int.ofNat (bits.foldl bitLsbStep state).1)) ∧
      out.locals.get? "x" = some (.int (Int.ofNat (bits.foldl bitLsbStep state).2.toNat)) := by
  induction bits generalizing frame state with
  | nil => exact ⟨frame, ExecBlock.nil, hr, hx⟩
  | cons b bs ih =>
    have hs := bitLsbStep_bounds state b
    simp only [List.sum_cons] at hle
    obtain ⟨mid, hm, hr', hx'⟩ := bitLsbStepSource (evm := evm) state b true hr hx hb (by omega)
    obtain ⟨out, ho, hr'', hx''⟩ := ih (bitLsbStep state b) hr' hx' (by omega) (by omega)
    exact ⟨out, ExecBlock.consNormal hm ho, hr'', hx''⟩

end Benchmarks.UniswapV3.Pool
