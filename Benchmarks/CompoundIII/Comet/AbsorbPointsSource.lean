import Benchmarks.CompoundIII.Comet.AbsorbPointsCountsSource
import Benchmarks.CompoundIII.Comet.AbsorbPointsSpendSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 2000

def absorbPointsLoad : Stmt :=
  .letDecl "points" (some (.tuple [.elem (.int (.uint ⟨32, by decide⟩)),
    .elem (.int (.uint ⟨64, by decide⟩)), .elem (.int (.uint ⟨128, by decide⟩)),
    .elem (.int (.uint ⟨32, by decide⟩))]))
    (.storage ⟨"liquidatorPoints", [.mindex (.var "absorber")]⟩)

def absorbPointsStore : Stmt :=
  .assign .storage ⟨"liquidatorPoints", [.mindex (.var "absorber")]⟩ (.var "points")

def absorbPointsBlock : List Stmt :=
  absorbPointsLoad :: (absorbPointsCountsBlock ++ (absorbPointsSpendBlock ++ [absorbPointsStore]))

theorem absorbPoints_source (frame : Frame) (evm : State) (addr : AccountAddress)
    (n gasUsed : UInt256) (accounts : List Value) (hc : frame.contract = contract)
    (ha : frame.locals.get? "absorber" = some (.address addr))
    (hac : frame.locals.get? "accounts" = some (.array accounts))
    (hg : frame.locals.get? "gasUsed" = some (.int gasUsed.toNat))
    (hp : frame.locals.get? "liquidatorPoints" = none)
    (hlen : accounts.length = n.toNat) (hn : n.toNat < 2^64) :
    internalBlockResult config frame evm absorbPointsBlock
      (absorbPointsOutcome evm addr n gasUsed) := by
  let p := absorbPointsLoaded evm addr
  let fee := UInt256.ofNat evm.executionEnv.header.baseFeePerGas
  let f1 : Frame := { frame with locals := frame.locals.insert "points" (liquidatorPointsValue p) }
  let f2 := absorbPointsCountsFrame f1 p n
  let f3 := absorbPointsSpendFrame f2 (absorbPointsCounts p n) gasUsed fee
  have hea : evalExpr? config frame evm (.var "absorber") = .ok (.address addr) := by
    simp only [evalExpr?, ha, EvalResult.ofOption]
  have hload : ExecStmt config frame evm absorbPointsLoad (.ok f1 evm) :=
    ExecStmt.letDecl (evalLiquidatorPoints frame evm addr _ hc hp hea)
  have hp1 : f1.locals.get? "points" = some (liquidatorPointsValue p) := by
    simp only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
    rfl
  have hac1 : f1.locals.get? "accounts" = some (.array accounts) := by
    simpa only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hac
  have hcounts := absorbPointsCounts_source f1 evm p n accounts hc hp1 hac1 hlen hn
  change internalBlockResult _ _ _ _
    (if AbsorbPointsValid p n gasUsed fee then
      if evm.executionEnv.perm then .ok (storeLiquidatorPoints evm addr
        (absorbPointsSpend (absorbPointsCounts p n) gasUsed fee)) else .staticViolation
    else .reverted)
  by_cases hcvalid : p.absorbs.toNat + 1 < 2^32 ∧ p.absorbed.toNat + n.toNat < 2^64
  · rw [if_pos hcvalid] at hcounts
    have hp2 : f2.locals.get? "points" = some (liquidatorPointsValue (absorbPointsCounts p n)) := by
      simp only [f2, absorbPointsCountsFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      rfl
    have hg2 : f2.locals.get? "gasUsed" = some (.int gasUsed.toNat) := by
      simpa only [f2, absorbPointsCountsFrame, f1, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hg
    have hspend := absorbPointsSpend_source f2 evm (absorbPointsCounts p n) gasUsed hc hp2 hg2
    change ExecBlock _ _ _ _ (if AbsorbPointsSpendValid p gasUsed fee then _ else _) at hspend
    by_cases hspvalid : AbsorbPointsSpendValid p gasUsed fee
    · rw [if_pos hspvalid] at hspend
      rw [if_pos (show AbsorbPointsValid p n gasUsed fee from ⟨hcvalid, hspvalid⟩)]
      have hp3 : f3.locals.get? "points" = some (liquidatorPointsValue
          (absorbPointsSpend (absorbPointsCounts p n) gasUsed fee)) := by
        simp only [f3, absorbPointsSpendFrame, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
        rfl
      have he3 : evalExpr? config f3 evm (.var "points") = .ok (liquidatorPointsValue
          (absorbPointsSpend (absorbPointsCounts p n) gasUsed fee)) := by
        simp only [evalExpr?, hp3, EvalResult.ofOption]
      have ha3 : f3.locals.get? "absorber" = some (.address addr) := by
        simpa only [f3, absorbPointsSpendFrame, f2, absorbPointsCountsFrame, f1,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using ha
      have headdr : evalExpr? config f3 evm (.var "absorber") = .ok (.address addr) := by
        simp only [evalExpr?, ha3, EvalResult.ofOption]
      have hloc3 : f3.locals.get? "liquidatorPoints" = none := by
        simpa only [f3, absorbPointsSpendFrame, f2, absorbPointsCountsFrame, f1,
          Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert] using hp
      have hc3 : f3.contract = contract := by
        simpa only [f3, absorbPointsSpendFrame, f2, absorbPointsCountsFrame, f1] using hc
      have hw := assignLiquidatorPoints f3 evm addr (.var "absorber")
        (absorbPointsSpend (absorbPointsCounts p n) gasUsed fee) hc3 hloc3 headdr
      cases hperm : evm.executionEnv.perm
      · simp only [Bool.false_eq_true, if_false, internalBlockResult]
        exact ExecBlock.consNormal hload (execBlock_append hcounts
          (execBlock_append hspend (ExecBlock.consStatic (ExecStmt.assignStatic he3 hw hperm))))
      · simp only [if_true, internalBlockResult]
        exact ⟨f3, ExecBlock.consNormal hload (execBlock_append hcounts
          (execBlock_append hspend (execBlock_singleton (ExecStmt.assign he3 hw))))⟩
    · rw [if_neg hspvalid] at hspend
      rw [if_neg (show ¬ AbsorbPointsValid p n gasUsed fee from fun hh ↦ hspvalid hh.2)]
      exact ExecBlock.consNormal hload (execBlock_append hcounts
        (execBlock_append_term hspend (by intro _ _ he; cases he)))
  · rw [if_neg hcvalid] at hcounts
    rw [if_neg (show ¬ AbsorbPointsValid p n gasUsed fee from fun hh ↦ hcvalid hh.1)]
    exact ExecBlock.consNormal hload (execBlock_append_term hcounts (by intro _ _ he; cases he))

end Benchmarks.CompoundIII.Comet
