import Benchmarks.UniswapV3.Pool.TickSqrtModel
import Benchmarks.UniswapV3.Pool.SourceWordBits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def tickSqrtBitExpr (mask : Nat) : Expr :=
  .binary .ne (.binary (.bitAnd (.uint ⟨256, by decide⟩))
    (.var "absTick") (.intLit (Int.ofNat mask))) (.intLit 0)

def tickSqrtMulExpr (factor : Nat) : Expr :=
  .binary (.shr (.uint ⟨256, by decide⟩))
    (.cast (.binary .mul (.var "ratio") (.intLit (Int.ofNat factor)))
      (.elem (.int (.uint ⟨256, by decide⟩)))) (.intLit 128)

def tickSqrtStepStmt (factor : Nat × Nat) : Stmt :=
  .ite (tickSqrtBitExpr factor.1)
    [.assign .localVar ⟨"ratio", []⟩ (tickSqrtMulExpr factor.2)] []

theorem evalTickSqrtBit {frame : Frame} {evm : EVM.State} (absTick : UInt256) (mask : Nat)
    (ha : frame.locals.get? "absTick" = some (.int (Int.ofNat absTick.toNat)))
    (hm : mask < UInt256.size) :
    evalExpr? config frame evm (tickSqrtBitExpr mask) =
      .ok (.bool (decide (UInt256.land absTick (UInt256.ofNat mask) ≠ ⟨0⟩))) := by
  have he := evalExpr_word_land (evalExpr_var_get (cfg := config) (evm := evm) ha)
    (a := absTick) (b := UInt256.ofNat mask)
    (rhs := .intLit (Int.ofNat mask))
    (by simp only [evalExpr?, pure, UInt256.toNat_ofNat_of_lt hm])
  have hz : (UInt256.land absTick (UInt256.ofNat mask)).toNat = 0 ↔
      UInt256.land absTick (UInt256.ofNat mask) = ⟨0⟩ := by
    exact ⟨uint256_toNat_eq_zero, fun h ↦ by rw [h]; rfl⟩
  simp only [tickSqrtBitExpr, evalExpr?, he, evalBinaryOp?, bind, EvalResult.bind, pure]
  simp [hz]
  apply Bool.eq_iff_iff.mpr
  simp [beq_iff_eq, hz]

theorem evalTickSqrtMul {frame : Frame} {evm : EVM.State} (ratio : UInt256) (factor : Nat)
    (hr : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat)))
    (hf : factor < UInt256.size) :
    evalExpr? config frame evm (tickSqrtMulExpr factor) =
      .ok (.int (Int.ofNat
        (UInt256.shiftRight (UInt256.mul (UInt256.ofNat factor) ratio) ⟨128⟩).toNat)) := by
  have hm := evalExpr_word_mul (evalExpr_var_get (cfg := config) (evm := evm) hr)
    (a := ratio) (b := UInt256.ofNat factor)
    (rhs := .intLit (Int.ofNat factor))
    (by simp only [evalExpr?, pure, UInt256.toNat_ofNat_of_lt hf])
  simpa only [tickSqrtMulExpr, u256_mul_comm] using evalExpr_word_shr 128 (by decide) hm

theorem tickSqrtStepSource {frame : Frame} {evm : EVM.State}
    (absTick ratio : UInt256) (factor : Nat × Nat)
    (ha : frame.locals.get? "absTick" = some (.int (Int.ofNat absTick.toNat)))
    (hr : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat)))
    (hf : factor.1 < UInt256.size ∧ factor.2 < UInt256.size) :
    ∃ frame', ExecStmt config frame evm (tickSqrtStepStmt factor) (.ok frame' evm) ∧
      frame'.locals.get? "ratio" = some (.int (Int.ofNat (tickSqrtStep absTick ratio factor).toNat)) ∧
      (∀ name, name ≠ "ratio" → frame'.locals.get? name = frame.locals.get? name) := by
  have he := evalTickSqrtBit (evm := evm) absTick factor.1 ha hf.1
  by_cases hz : UInt256.land absTick (UInt256.ofNat factor.1) = ⟨0⟩
  · refine ⟨frame, ExecStmt.iteFalse ?_ ExecBlock.nil, ?_, fun _ _ ↦ rfl⟩
    · simpa only [hz, ne_eq, not_true_eq_false, decide_false] using he
    · simpa only [tickSqrtStep, hz, ↓reduceIte] using hr
  · let out : Frame :=
      {frame with
        locals := frame.locals.insert "ratio"
          (.int (Int.ofNat (tickSqrtStep absTick ratio factor).toNat))}
    refine ⟨out, ?_, ?_, ?_⟩
    · refine ExecStmt.iteTrue ?_ (ExecBlock.consNormal
        (ExecStmt.assign (value := .int (Int.ofNat (tickSqrtStep absTick ratio factor).toNat))
          ?_ ?_) ExecBlock.nil)
      · simpa only [hz, ne_eq, not_false_eq_true, decide_true] using he
      · simpa only [tickSqrtStep, if_neg hz] using evalTickSqrtMul ratio factor.2 hr hf.2
      · exact assignLocalVarBase_frame hr
    · simp [out]
    · intro name hn
      simp [out, Std.HashMap.getElem?_insert, Ne.symm hn]

theorem tickSqrtFoldSource {frame : Frame} {evm : EVM.State}
    (absTick ratio : UInt256) (factors : List (Nat × Nat))
    (ha : frame.locals.get? "absTick" = some (.int (Int.ofNat absTick.toNat)))
    (hr : frame.locals.get? "ratio" = some (.int (Int.ofNat ratio.toNat)))
    (hf : ∀ f ∈ factors, f.1 < UInt256.size ∧ f.2 < UInt256.size) :
    ∃ frame', ExecBlock config frame evm (factors.map tickSqrtStepStmt) (.ok frame' evm) ∧
      frame'.locals.get? "ratio" =
        some (.int (Int.ofNat (factors.foldl (tickSqrtStep absTick) ratio).toNat)) ∧
      (∀ name, name ≠ "ratio" → frame'.locals.get? name = frame.locals.get? name) := by
  induction factors generalizing frame ratio with
  | nil => exact ⟨frame, ExecBlock.nil, hr, fun _ _ ↦ rfl⟩
  | cons f fs ih =>
    obtain ⟨mid, hs, hm, hp⟩ := tickSqrtStepSource (evm := evm)
      absTick ratio f ha hr (hf f (by simp))
    obtain ⟨out, hb, ho, hpres⟩ := ih (tickSqrtStep absTick ratio f)
      (by rw [hp "absTick" (by decide)]; exact ha) hm
      (fun f hf' ↦ hf f (by simp [hf']))
    exact ⟨out, ExecBlock.consNormal hs hb, ho, fun name hn ↦ (hpres name hn).trans (hp name hn)⟩

end Benchmarks.UniswapV3.Pool
