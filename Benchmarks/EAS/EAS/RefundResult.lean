import Benchmarks.EAS.EAS.BytesAllocation

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def refundNext (heap size : Nat) : Nat := if size = 0 then heap else allocateNext heap (bytesAllocation size)
def refundAllocationValid (heap size : Nat) : Prop := size = 0 ∨
  (size ≤ 2^64-1 ∧ allocateNext heap (bytesAllocation size) ≤ 2^64-1 ∧ heap ≤ allocateNext heap (bytesAllocation size))
instance (heap size : Nat) : Decidable (refundAllocationValid heap size) :=
  inferInstanceAs (Decidable (_ ∨ _ ∧ _ ∧ _))

def refundResultLength : Expr := .arrayLength .localVar {base := "result"}
def refundAllocationStmt : Stmt := .ite (.binary .ne refundResultLength (.intLit 0))
  (.require (.binary .le refundResultLength (.intLit 18446744073709551615)) ::
    allocateBlock (bytesAllocationExpr refundResultLength)) []

def refundAllocationLocals (locals : Store) (heap size : Nat) : Store :=
  if size = 0 then locals else allocateBlockLocals locals (allocateNext heap (bytesAllocation size))

theorem refundResultLength_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (ho : frame.locals.get? "result" = some (.bytes out)) :
    evalExpr? cfg frame evm refundResultLength = .ok (.int (Int.ofNat out.size)) := by
  simp only [refundResultLength, evalExpr?, readLocalPath?, ho, EvalResult.bind, bind, pure]

theorem refundResultNonempty_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (ho : frame.locals.get? "result" = some (.bytes out)) :
    evalExpr? cfg frame evm (.binary .ne refundResultLength (.intLit 0)) = .ok (.bool (decide (out.size ≠ 0))) := by
  simp only [evalExpr?, refundResultLength_eval ho, pure, bind, EvalResult.bind, evalBinaryOp?]
  congr 2
  apply Bool.eq_iff_iff.mpr
  simp [Value.int.injEq, Int.ofNat_eq_natCast]

theorem refundResultBound_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (ho : frame.locals.get? "result" = some (.bytes out)) :
    evalExpr? cfg frame evm (.binary .le refundResultLength (.intLit 18446744073709551615)) =
      .ok (.bool (decide (out.size ≤ 2^64-1))) := by
  have he : (Int.ofNat out.size ≤ (18446744073709551615 : Int)) = (out.size ≤ 2^64-1) := by
    apply propext
    simp only [Int.ofNat_eq_natCast]
    omega
  simp only [evalExpr?, refundResultLength_eval ho, pure, bind, EvalResult.bind, evalBinaryOp?, he]

theorem refundAllocationSource {cfg : Config} {locals imms : Store} {evm : EVM.State} {out : ByteArray} {heap : Nat}
    (ho : locals.get? "result" = some (.bytes out))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if refundAllocationValid heap out.size then
      ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm refundAllocationStmt
        (.ok {contract := contract, locals := refundAllocationLocals locals heap out.size, immutables := imms} evm)
    else ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm refundAllocationStmt .reverted := by
  have hn := refundResultNonempty_eval (cfg := cfg) (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm) ho
  have hb := refundResultBound_eval (cfg := cfg) (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm) ho
  have hs := bytesAllocationExpr_eval (refundResultLength_eval (cfg := cfg)
    (frame := {contract := contract, locals := locals, immutables := imms}) (evm := evm) ho)
  by_cases hz : out.size = 0
  · have hv : refundAllocationValid heap out.size := Or.inl hz
    rw [if_pos hv, refundAllocationLocals, if_pos hz]
    exact ExecStmt.iteFalse (by simpa only [hz, ne_self_iff_false, decide_false] using hn) ExecBlock.nil
  · have hne : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
        (.binary .ne refundResultLength (.intLit 0)) = .ok (.bool true) := by
      simpa only [decide_eq_true hz] using hn
    by_cases hv : refundAllocationValid heap out.size
    · rw [if_pos hv, refundAllocationLocals, if_neg hz]
      have hg := hv.resolve_left hz
      exact ExecStmt.iteTrue hne (ExecBlock.consNormal
        (ExecStmt.requireTrue (by simpa only [hg.1, decide_true] using hb)) (allocateBlock_ok hs hh hg.2))
    · rw [if_neg hv]
      apply ExecStmt.iteTrue hne
      by_cases hl : out.size ≤ 2^64-1
      · apply ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [hl, decide_true] using hb))
        exact allocateBlock_revert hs hh (fun hg => hv (Or.inr ⟨hl,hg⟩))
      · exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [hl, decide_false] using hb))

theorem refundAllocationLocals_heap {locals : Store} {heap size : Nat}
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    (refundAllocationLocals locals heap size).get? "$EAS.freeMemory" = some (.int (Int.ofNat (refundNext heap size))) := by
  unfold refundAllocationLocals refundNext
  split
  · exact hh
  · exact store_get_self _ _ _

theorem refundAllocationLocals_ok (locals : Store) (heap size : Nat) :
    (refundAllocationLocals locals heap size).get? "ok" = locals.get? "ok" := by
  unfold refundAllocationLocals
  split
  · rfl
  · exact allocateBlockLocals_get (by decide) (by decide) (by decide)

def refundResultValid (heap : Nat) (success : Bool) (out : ByteArray) : Prop :=
  success = true ∧ refundAllocationValid heap out.size
instance (heap : Nat) (success : Bool) (out : ByteArray) : Decidable (refundResultValid heap success out) :=
  inferInstanceAs (Decidable (_ ∧ _))

def refundResultTail : Body := [refundAllocationStmt, .require (.var "ok")]

theorem refundResultSource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {out : ByteArray} {success : Bool} {heap : Nat}
    (ho : locals.get? "result" = some (.bytes out)) (hok : locals.get? "ok" = some (.bool success))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if refundResultValid heap success out then
      ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm refundResultTail
        (.ok {contract := contract, locals := refundAllocationLocals locals heap out.size, immutables := imms} evm)
    else ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm refundResultTail .reverted := by
  have ha := refundAllocationSource (fork := fork) (cfg := cfg) (imms := imms) (evm := evm) ho hh
  have he : evalExpr? cfg {contract := contract, locals := refundAllocationLocals locals heap out.size, immutables := imms}
      evm (.var "ok") = .ok (.bool success) := by
    simp only [evalExpr?, refundAllocationLocals_ok, hok, EvalResult.ofOption]
  by_cases hv : refundResultValid heap success out
  · rw [if_pos hv]
    rw [if_pos hv.2] at ha
    rw [hv.1] at he
    exact ExecBlock.consNormal ha (ExecBlock.consNormal (ExecStmt.requireTrue he) ExecBlock.nil)
  · rw [if_neg hv]
    by_cases hg : refundAllocationValid heap out.size
    · rw [if_pos hg] at ha
      have hf : success = false := by cases success <;> simp_all [refundResultValid]
      rw [hf] at he
      exact ExecBlock.consNormal ha (ExecBlock.consRevert (ExecStmt.requireFalse he))
    · rw [if_neg hg] at ha
      exact ExecBlock.consRevert ha

end Benchmarks.EAS.EAS
