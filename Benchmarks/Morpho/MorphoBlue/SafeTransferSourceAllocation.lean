import Benchmarks.Morpho.MorphoBlue.StateBlock
import Benchmarks.Morpho.MorphoBlue.Common
import Benchmarks.Morpho.MorphoBlue.LocalBytesGuard

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.Morpho.MorphoBlue
set_option maxRecDepth 1000

abbrev safeTransferFunction : FunctionDecl := contract.functions[19]!
abbrev safeTransferFromFunction : FunctionDecl := contract.functions[20]!
def safeTransferTail : List Stmt := safeTransferFunction.body.drop 4

-- Both calldata encoders share exactly the same post-call source logic.
theorem safeTransferFrom_tail : safeTransferFromFunction.body.drop 4 = safeTransferTail := rfl

def safeTransferRetLength : Expr := .arrayLength .localVar ⟨"returndata", []⟩
def safeTransferCap (e : Expr) : Expr := .binary .le e
  (.binary .sub (.binary .exp (.intLit 2) (.intLit 64)) (.intLit 1))
def safeTransferHasReturn : Expr := .binary .ne safeTransferRetLength (.intLit 0)

def safeTransferReturnAlloc (n : Nat) : Nat := if n = 0 then 0 else 32 + (n + 31) / 32 * 32

theorem safeTransferRetLength_eval {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? config frame evm safeTransferRetLength = .ok (.int (Int.ofNat out.size)) := by
  simp only [safeTransferRetLength, evalExpr?, hout, readLocalPath?, pure, bind, EvalResult.bind]

theorem safeTransferCap_eval {frame : Frame} {evm : EVM.State} {e : Expr} {n : Nat}
    (he : evalExpr? config frame evm e = .ok (.int (Int.ofNat n))) :
    evalExpr? config frame evm (safeTransferCap e) =
      .ok (.bool (decide (n ≤ 2 ^ 64 - 1))) := by
  simp only [safeTransferCap, evalExpr?, he, pure, bind, EvalResult.bind, evalBinaryOp?]
  norm_num [Int.toNat]

theorem safeTransferHasReturn_eval {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? config frame evm safeTransferHasReturn =
      .ok (.bool (decide (out.size ≠ 0))) :=
  evalLocalBytesLengthNeZero hout

theorem safeTransferTail_oversize {frame : Frame} {evm : EVM.State} {out : ByteArray}
    (hout : frame.locals.get? "returndata" = some (.bytes out)) (hb : 2 ^ 64 ≤ out.size) :
    ExecBlock config frame evm safeTransferTail .reverted := by
  have hn : out.size ≠ 0 := by omega
  apply ExecBlock.consRevert (ExecStmt.iteTrue ?_ ?_)
  · exact (safeTransferHasReturn_eval hout).trans (by rw [decide_eq_true hn])
  · apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    exact (safeTransferCap_eval (safeTransferRetLength_eval hout)).trans
      (by rw [decide_eq_false (by omega)])

def safeTransferCopyCursor : Expr := .binary .add
  (.binary .add (.var "__memory") (.intLit 32))
  (.binary .mul (.binary .div (.binary .add safeTransferRetLength (.intLit 31))
    (.intLit 32)) (.intLit 32))

theorem safeTransferMemoryAdd_eval {frame : Frame} {evm : EVM.State} {n : Nat}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n))) (d : Nat) :
    evalExpr? config frame evm (.binary .add (.var "__memory") (.intLit (Int.ofNat d))) =
      .ok (.int (Int.ofNat (n + d))) := by
  simp only [evalExpr?, hm, EvalResult.ofOption, evalBinaryOp?, pure, bind, EvalResult.bind]
  rfl

theorem safeTransferCopyCursor_eval {frame : Frame} {evm : EVM.State} {n : Nat}
    {out : ByteArray} (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out)) :
    evalExpr? config frame evm safeTransferCopyCursor =
      .ok (.int (Int.ofNat (n + 32 + (out.size + 31) / 32 * 32))) := by
  simp only [safeTransferCopyCursor, evalExpr?, hm, EvalResult.ofOption,
    safeTransferRetLength_eval hout, evalBinaryOp?, pure, bind, EvalResult.bind]
  norm_num [Int.tdiv]

theorem safeTransferTail_allocationPrefix_preserves {frame : Frame} {evm : EVM.State}
    {n : Nat} {out : ByteArray}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out)) (hb : out.size < 2 ^ 64) :
    ∃ frame', ABlock config evm frame safeTransferTail frame' (safeTransferTail.drop 2) ∧
      frame'.locals.get? "__memory" =
        some (.int (Int.ofNat (n + safeTransferReturnAlloc out.size + 128))) ∧
      (∀ name, name ≠ "__memory" → frame'.locals.get? name = frame.locals.get? name) := by
  by_cases hz : out.size = 0
  · have ht : evalExpr? config frame evm safeTransferHasReturn = .ok (.bool false) :=
      (safeTransferHasReturn_eval hout).trans (by rw [decide_eq_false (not_not.mpr hz)])
    have hi : ExecStmt config frame evm safeTransferTail[0]! (.ok frame evm) :=
      .iteFalse ht .nil
    let frame' := { frame with locals := frame.locals.insert "__memory" (.int (Int.ofNat (n + 128))) }
    have ha : ExecStmt config frame evm safeTransferTail[1]! (.ok frame' evm) :=
      .assign (safeTransferMemoryAdd_eval hm 128) (assignLocalWord hm)
    refine ⟨frame', ⟨fun hh ↦ .consNormal hi (.consNormal ha hh)⟩, ?_, ?_⟩
    · simp only [frame', store_get_self, safeTransferReturnAlloc, hz, ↓reduceIte, Nat.add_zero]
    · intro name hname
      exact store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using Ne.symm hname)
  · let m := n + 32 + (out.size + 31) / 32 * 32
    let mid := { frame with locals := frame.locals.insert "__memory" (.int (Int.ofNat m)) }
    have ht : evalExpr? config frame evm safeTransferHasReturn = .ok (.bool true) :=
      (safeTransferHasReturn_eval hout).trans (by rw [decide_eq_true hz])
    have hc : evalExpr? config frame evm (safeTransferCap safeTransferRetLength) =
        .ok (.bool true) := (safeTransferCap_eval (safeTransferRetLength_eval hout)).trans
          (by rw [decide_eq_true (by omega)])
    have he : ExecStmt config frame evm (.assign .localVar ⟨"__memory", []⟩ safeTransferCopyCursor)
        (.ok mid evm) := .assign (safeTransferCopyCursor_eval hm hout) (assignLocalWord hm)
    have hi : ExecStmt config frame evm safeTransferTail[0]! (.ok mid evm) :=
      .iteTrue ht (.consNormal (.requireTrue hc) (.consNormal he .nil))
    have hmm : mid.locals.get? "__memory" = some (.int (Int.ofNat m)) := store_get_self _ _ _
    let frame' := { mid with locals := mid.locals.insert "__memory" (.int (Int.ofNat (m + 128))) }
    have ha : ExecStmt config mid evm safeTransferTail[1]! (.ok frame' evm) :=
      .assign (safeTransferMemoryAdd_eval hmm 128) (assignLocalWord hmm)
    refine ⟨frame', ⟨fun hh ↦ .consNormal hi (.consNormal ha hh)⟩, ?_, ?_⟩
    · rw [show frame'.locals.get? "__memory" = some (.int (Int.ofNat (m + 128)))
        from store_get_self _ _ _]
      simp only [m, safeTransferReturnAlloc, if_neg hz, Nat.add_assoc]

    · intro name hname
      dsimp only [frame', mid]
      rw [store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using Ne.symm hname),
        store_get_ne _ _ (by simpa only [beq_eq_false_iff_ne] using Ne.symm hname)]

theorem safeTransferTail_allocationPrefix {frame : Frame} {evm : EVM.State}
    {n : Nat} {out : ByteArray}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out)) (hb : out.size < 2 ^ 64) :
    ∃ frame', ABlock config evm frame safeTransferTail frame' (safeTransferTail.drop 2) ∧
      frame'.locals.get? "__memory" =
        some (.int (Int.ofNat (n + safeTransferReturnAlloc out.size + 128))) := by
  obtain ⟨frame', hp, hm', _⟩ := safeTransferTail_allocationPrefix_preserves hm hout hb
  exact ⟨frame', hp, hm'⟩

theorem safeTransferTail_allocationRevert {frame : Frame} {evm : EVM.State}
    {n : Nat} {out : ByteArray}
    (hm : frame.locals.get? "__memory" = some (.int (Int.ofNat n)))
    (hout : frame.locals.get? "returndata" = some (.bytes out)) (hb : out.size < 2 ^ 64)
    (hcap : 2 ^ 64 ≤ n + safeTransferReturnAlloc out.size + 128) :
    ExecBlock config frame evm safeTransferTail .reverted := by
  obtain ⟨frame', hp, hm'⟩ := safeTransferTail_allocationPrefix hm hout hb
  apply hp.run (ExecBlock.consRevert (.requireFalse ?_))
  have he : evalExpr? config frame' evm (.var "__memory") =
      .ok (.int (Int.ofNat (n + safeTransferReturnAlloc out.size + 128))) := by
    simp only [evalExpr?, hm', EvalResult.ofOption]
  exact (safeTransferCap_eval he).trans (by rw [decide_eq_false (by omega)])

end Benchmarks.Morpho.MorphoBlue
