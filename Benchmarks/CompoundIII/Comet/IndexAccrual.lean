import Benchmarks.CompoundIII.Comet.ArithmeticSource
import Benchmarks.CompoundIII.Comet.NarrowArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def indexIncrement (index rate elapsed : UInt256) : UInt256 :=
  mulFactorWord index (UInt256.mul rate elapsed)

def accruedIndexWord (index rate elapsed : UInt256) : UInt256 :=
  index + indexIncrement index rate elapsed

abbrev IndexAccrualValid (index rate elapsed : UInt256) : Prop :=
  (indexIncrement index rate elapsed).toNat < 2^64 ∧
  index.toNat + (indexIncrement index rate elapsed).toNat < 2^64

theorem rateTimeProduct_lt {rate elapsed : UInt256}
    (hr : rate.toNat < 2^64) (ht : elapsed.toNat < 2^40) :
    rate.toNat * elapsed.toNat < 2^104 := by
  calc
    _ < 2^64 * 2^40 := Nat.mul_lt_mul_of_lt_of_lt hr ht
    _ = _ := by decide

theorem indexFactorProduct_lt {index rate elapsed : UInt256}
    (hi : index.toNat < 2^64) (hr : rate.toNat < 2^64) (ht : elapsed.toNat < 2^40) :
    index.toNat * (UInt256.mul rate elapsed).toNat < UInt256.size := by
  have hm := rateTimeProduct_lt hr ht
  rw [u256_mul_toNat, Nat.mod_eq_of_lt (lt_trans hm (by decide))]
  calc
    _ < 2^64 * 2^104 := Nat.mul_lt_mul_of_lt_of_lt hi hm
    _ < UInt256.size := by decide

theorem accruedIndexWord_lt {index rate elapsed : UInt256}
    (h : IndexAccrualValid index rate elapsed) :
    (accruedIndexWord index rate elapsed).toNat < 2^64 := by
  have he : (index + indexIncrement index rate elapsed).toNat =
      index.toNat + (indexIncrement index rate elapsed).toNat :=
    addWord_toNat _ _ (lt_trans h.2 (by decide))
  change (index + indexIncrement index rate elapsed).toNat < _
  rw [he]
  exact h.2

def indexLocalName (borrow : Bool) : Ident :=
  if borrow then "baseBorrowIndex_" else "baseSupplyIndex_"

def indexRateName (borrow : Bool) : Ident := if borrow then "borrowRate" else "supplyRate"
def indexMulName (borrow : Bool) : Ident := if borrow then "__c5" else "__c3"
def indexSafeName (borrow : Bool) : Ident := if borrow then "__c6" else "__c4"

def indexAccrualBlock (borrow : Bool) : List Stmt :=
  [.internalCall "mulFactor" [.var (indexLocalName borrow),
      .inRange (.uint ⟨256, by decide⟩)
        (.binary .mul (.var (indexRateName borrow)) (.var "timeElapsed"))] (indexMulName borrow),
    .internalCall "safe64" [.var (indexMulName borrow)] (indexSafeName borrow),
    .assign .localVar ⟨indexLocalName borrow, []⟩
      (.inRange (.uint ⟨64, by decide⟩)
        (.binary .add (.var (indexLocalName borrow)) (.var (indexSafeName borrow))))]

def indexAccrualFrame (frame : Frame) (borrow : Bool) (index rate elapsed : UInt256) : Frame :=
  let delta := indexIncrement index rate elapsed
  { frame with
    locals := ((frame.locals.insert (indexMulName borrow) (.int delta.toNat)).insert
      (indexSafeName borrow) (.int delta.toNat)).insert
        (indexLocalName borrow) (.int (accruedIndexWord index rate elapsed).toNat) }

-- GENERALIZES Reasoning.SolmArithmetic.assignLocalVarBase_ok to frames with immutables.
theorem assignLocalFrame {cfg : Config} {frame : Frame} {evm : EVM.State}
    {name : Ident} {old value : Value} (hget : frame.locals.get? name = some old) :
    assignStorageRef? cfg frame evm .localVar ⟨name, []⟩ value =
      .ok ({ frame with locals := frame.locals.insert name value }, evm) := by
  simp only [assignStorageRef?, updateLocalPath?, EvalResult.bind, bind, pure]
  change (match frame.locals.get? name with
    | some _ => EvalResult.ok ({ frame with locals := frame.locals.insert name value }, evm)
    | none => EvalResult.error EvalError.unboundVariable) = _
  rw [hget]

theorem indexAccrualBlock_result (frame : Frame) (evm : EVM.State) (borrow : Bool)
    (index rate elapsed : UInt256) (hc : frame.contract = contract)
    (hi : frame.locals.get? (indexLocalName borrow) = some (.int index.toNat))
    (hr : frame.locals.get? (indexRateName borrow) = some (.int rate.toNat))
    (ht : frame.locals.get? "timeElapsed" = some (.int elapsed.toNat))
    (hib : index.toNat < 2^64) (hrb : rate.toNat < 2^64) (htb : elapsed.toNat < 2^40) :
    ExecBlock config frame evm (indexAccrualBlock borrow)
      (if IndexAccrualValid index rate elapsed then
        .ok (indexAccrualFrame frame borrow index rate elapsed) evm else .reverted) := by
  have hei : evalExpr? config frame evm (.var (indexLocalName borrow)) =
      .ok (.int (Int.ofNat index.toNat)) := by simp only [evalExpr?, hi, EvalResult.ofOption, Int.ofNat_eq_natCast]
  have her : evalExpr? config frame evm (.var (indexRateName borrow)) =
      .ok (.int (Int.ofNat rate.toNat)) := by simp only [evalExpr?, hr, EvalResult.ofOption, Int.ofNat_eq_natCast]
  have het : evalExpr? config frame evm (.var "timeElapsed") =
      .ok (.int (Int.ofNat elapsed.toNat)) := by simp only [evalExpr?, ht, EvalResult.ofOption, Int.ofNat_eq_natCast]
  have hem := checkedMulSourceOk her het (lt_trans (rateTimeProduct_lt hrb htb) (by decide))
  let delta := indexIncrement index rate elapsed
  let f1 : Frame := { frame with locals := frame.locals.insert (indexMulName borrow) (.int delta.toNat) }
  apply ExecBlock.consNormal (mulFactor_call_ok frame evm index (UInt256.mul rate elapsed)
    _ _ (indexMulName borrow) hc hei hem (indexFactorProduct_lt hib hrb htb))
  have hed : evalExpr? config f1 evm (.var (indexMulName borrow)) =
      .ok (.int (Int.ofNat delta.toNat)) := by
    simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_self_eq_true, if_true, EvalResult.ofOption]
    rfl
  by_cases hs : delta.toNat < 2^64
  · let f2 : Frame := { f1 with locals := f1.locals.insert (indexSafeName borrow) (.int delta.toNat) }
    apply ExecBlock.consNormal (safe64_call_ok f1 evm delta _ (indexSafeName borrow) hc hed hs)
    have hig : f2.locals.get? (indexLocalName borrow) = some (.int index.toNat) := by
      cases borrow <;> simpa [f2, f1, indexMulName, indexSafeName, indexLocalName,
        Std.HashMap.getElem?_insert] using hi
    have heib : evalExpr? config f2 evm (.var (indexLocalName borrow)) =
        .ok (.int (Int.ofNat index.toNat)) := by simp only [evalExpr?, hig, EvalResult.ofOption, Int.ofNat_eq_natCast]
    have hedb : evalExpr? config f2 evm (.var (indexSafeName borrow)) =
        .ok (.int (Int.ofNat delta.toNat)) := by
      simp only [evalExpr?, f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        beq_self_eq_true, if_true, EvalResult.ofOption]
      rfl
    by_cases ha : index.toNat + delta.toNat < 2^64
    · simp only [IndexAccrualValid, show indexIncrement index rate elapsed = delta from rfl,
        hs, ha, and_self, if_true]
      apply ExecBlock.consNormal (ExecStmt.assign
        (checkedNarrowAddSourceOk ⟨64, by decide⟩ (by decide) heib hedb ha)
        (assignLocalFrame hig))
      exact ExecBlock.nil
    · simp only [IndexAccrualValid, show indexIncrement index rate elapsed = delta from rfl,
        ha, and_false, if_false]
      apply ExecBlock.consRevert
      exact ExecStmt.assignExprRevert
        (uintRangeSourceOverflow ⟨64, by decide⟩ (naturalAddSource heib hedb) (Nat.le_of_not_gt ha))
  · simp only [IndexAccrualValid, show indexIncrement index rate elapsed = delta from rfl,
      hs, false_and, if_false]
    exact ExecBlock.consRevert (safe64_call_revert f1 evm delta _ (indexSafeName borrow) hc hed hs)

end Benchmarks.CompoundIII.Comet
