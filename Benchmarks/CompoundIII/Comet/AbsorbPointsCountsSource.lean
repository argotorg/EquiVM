import Benchmarks.CompoundIII.Comet.AbsorbPointsModel
import Benchmarks.CompoundIII.Comet.NarrowArithmetic
import Benchmarks.CompoundIII.Comet.ArithmeticSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbPointsCountsBlock : List Stmt :=
  [.assign .localVar ⟨"points", [.field "numAbsorbs"]⟩
      (.inRange (.uint ⟨32, by decide⟩)
        (.binary .add (.field (.var "points") "numAbsorbs") (.intLit 1))),
    .internalCall "safe64" [.arrayLength .localVar ⟨"accounts", []⟩] "__c3",
    .assign .localVar ⟨"points", [.field "numAbsorbed"]⟩
      (.inRange (.uint ⟨64, by decide⟩)
        (.binary .add (.field (.var "points") "numAbsorbed") (.var "__c3")))]

def absorbPointsCountsFrame (frame : Frame) (p : LiquidatorPointsData) (n : UInt256) : Frame :=
  { frame with
    locals := ((frame.locals.insert "points"
      (liquidatorPointsValue (liquidatorPointsSet p 0 (p.absorbs + ⟨1⟩)))).insert "__c3"
        (.int n.toNat)).insert "points" (liquidatorPointsValue (absorbPointsCounts p n)) }

theorem absorbPointsCounts_source (frame : Frame) (evm : State) (p : LiquidatorPointsData)
    (n : UInt256) (accounts : List Value) (hc : frame.contract = contract)
    (hp : frame.locals.get? "points" = some (liquidatorPointsValue p))
    (ha : frame.locals.get? "accounts" = some (.array accounts))
    (hlen : accounts.length = n.toNat) (hn : n.toNat < 2^64) :
    ExecBlock config frame evm absorbPointsCountsBlock
      (if p.absorbs.toNat + 1 < 2^32 ∧ p.absorbed.toNat + n.toNat < 2^64 then
        .ok (absorbPointsCountsFrame frame p n) evm else .reverted) := by
  have he : evalExpr? config frame evm (.var "points") = .ok (liquidatorPointsValue p) := by
    simp only [evalExpr?, hp, EvalResult.ofOption]
  have hone : evalExpr? config frame evm (.intLit 1) =
      .ok (.int (UInt256.ofNat 1).toNat) := by simp only [evalExpr?, pure]; rfl
  by_cases hi : p.absorbs.toNat + 1 < 2^32
  · let p1 := liquidatorPointsSet p 0 (p.absorbs + ⟨1⟩)
    let f1 : Frame := { frame with locals := frame.locals.insert "points" (liquidatorPointsValue p1) }
    let f2 : Frame := { f1 with locals := f1.locals.insert "__c3" (.int n.toNat) }
    have hinc := checkedNarrowAddSourceOk ⟨32, by decide⟩ (by decide)
      (evalLiquidatorPointsLocalField 0 he) hone hi
    have hstep : ExecStmt config frame evm absorbPointsCountsBlock[0]!
        (.ok f1 evm) := ExecStmt.assign hinc (assignLiquidatorPointsLocalField 0 _ hp)
    have halen : evalExpr? config f1 evm (.arrayLength .localVar ⟨"accounts", []⟩) =
        .ok (.int n.toNat) := by
      have ha' := ha
      simp only [Std.HashMap.get?_eq_getElem?] at ha'
      simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        ha', readLocalPath?, pure, bind, EvalResult.bind]
      change EvalResult.ok (Value.int accounts.length) = EvalResult.ok (Value.int n.toNat)
      rw [hlen]
    have hcall := safe64_call_ok f1 evm n _ "__c3" hc halen hn
    have hp2 : f2.locals.get? "points" = some (liquidatorPointsValue p1) := by
      simp only [f2, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      rfl
    have he2 : evalExpr? config f2 evm (.var "points") = .ok (liquidatorPointsValue p1) := by
      simp only [evalExpr?, hp2, EvalResult.ofOption]
    have hn2 : evalExpr? config f2 evm (.var "__c3") = .ok (.int n.toNat) := by
      simp only [evalExpr?, f2, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    by_cases hj : p.absorbed.toNat + n.toNat < 2^64
    · rw [if_pos ⟨hi, hj⟩]
      have hadd := checkedNarrowAddSourceOk ⟨64, by decide⟩ (by decide)
        (evalLiquidatorPointsLocalField 1 he2) hn2 hj
      exact ExecBlock.consNormal hstep (ExecBlock.consNormal hcall
        (ExecBlock.consNormal (ExecStmt.assign hadd
          (assignLiquidatorPointsLocalField 1 (p.absorbed + n) hp2)) ExecBlock.nil))
    · rw [if_neg (fun hh ↦ hj hh.2)]
      have hadd := uintRangeSourceOverflow ⟨64, by decide⟩
        (naturalAddSource (evalLiquidatorPointsLocalField 1 he2) hn2) (le_of_not_gt hj)
      exact ExecBlock.consNormal hstep (ExecBlock.consNormal hcall
        (ExecBlock.consRevert (ExecStmt.assignExprRevert hadd)))
  · rw [if_neg (fun hh ↦ hi hh.1)]
    exact ExecBlock.consRevert (ExecStmt.assignExprRevert
      (uintRangeSourceOverflow ⟨32, by decide⟩
        (naturalAddSource (evalLiquidatorPointsLocalField 0 he) hone) (le_of_not_gt hi)))

end Benchmarks.CompoundIII.Comet
