import Benchmarks.Morpho.MetaMorphoV1_1.AccruedAssetsQueueSource

/-! Loop locals, checked accumulation, and preservation of the later fee-calculation locals. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure AccruedAssetsLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (i total cursor : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Morpho.MetaMorphoV1_1.contract
  imms : frame.immutables = immStore v
  index : frame.locals.get? "i" = some (uint256Value i)
  total : frame.locals.get? "realTotalAssets" = some (uint256Value total)
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)
  queue : frame.locals.get? "withdrawQueue" = none

def AccruedAssetsPreserves (before after : Frame) : Prop :=
  ∀ name, ("__c0" == name) = false → ("__c1" == name) = false →
    (cursorName == name) = false → (slotsAndCursorName == name) = false →
    ("realTotalAssets" == name) = false → ("i" == name) = false →
    after.locals.get? name = before.locals.get? name

theorem AccruedAssetsPreserves.refl (frame : Frame) : AccruedAssetsPreserves frame frame :=
  fun _ _ _ _ _ _ _ ↦ rfl

theorem AccruedAssetsPreserves.trans {a b c : Frame}
    (hab : AccruedAssetsPreserves a b) (hbc : AccruedAssetsPreserves b c) :
    AccruedAssetsPreserves a c := by
  intro name h0 h1 hc ht hr hi
  exact (hbc name h0 h1 hc ht hr hi).trans (hab name h0 h1 hc ht hr hi)

theorem accruedAssetsReaderPreserves (frame : Frame) (name : Ident) (value : Value)
    (ptr : UInt256) (hname : name = "__c0" ∨ name = "__c1") :
    AccruedAssetsPreserves frame (cursorResultFrame frame name value ptr) := by
  intro key h0 h1 hc ht _ _
  apply cursorResultFrame_preserves _ _ _ _ _ hc _ ht
  rcases hname with rfl | rfl
  · exact h0
  · exact h1

theorem AccruedAssetsLocals.reader {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i total cursor : UInt256} (h : AccruedAssetsLocals v frame i total cursor)
    (name : Ident) (value : Value) (ptr : UInt256)
    (hi : (name == "i") = false) (ht : (name == "realTotalAssets") = false)
    (hq : (name == "withdrawQueue") = false) :
    AccruedAssetsLocals v (cursorResultFrame frame name value ptr) i total ptr := by
  refine ⟨h.contract, h.imms, ?_, ?_, cursorResultFrame_cursor _ _ _ _, ?_⟩
  · rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) hi (by decide)]
    exact h.index
  · rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) ht (by decide)]
    exact h.total
  · rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) hq (by decide)]
    exact h.queue

def accruedAssetsTotalFrame (frame : Frame) (total assets : UInt256) : Frame :=
  { frame with locals := frame.locals.insert "realTotalAssets" (uint256Value (total + assets)) }

theorem accruedAssetsSumSource {frame : Frame} {evm : State} {total assets : UInt256}
    (ht : frame.locals.get? "realTotalAssets" = some (uint256Value total))
    (ha : frame.locals.get? "__c1" = some (uint256Value assets))
    (hfit : total.toNat + assets.toNat < UInt256.size) :
    ExecStmt config frame evm accruedAssetsIteration[6]!
      (.ok (accruedAssetsTotalFrame frame total assets) evm) := by
  apply ExecStmt.assign (checkedAddSourceOk ?_ ?_ hfit)
  · simp only [assignStorageRef?, ht, updateLocalPath?, EvalResult.ofOption,
      bind, EvalResult.bind, pure]
    rfl
  · simp only [evalExpr?, ht, EvalResult.ofOption]
  · simp only [evalExpr?, ha, EvalResult.ofOption]

theorem accruedAssetsSumReverts {frame : Frame} {evm : State} {total assets : UInt256}
    (ht : frame.locals.get? "realTotalAssets" = some (uint256Value total))
    (ha : frame.locals.get? "__c1" = some (uint256Value assets))
    (hbad : UInt256.size ≤ total.toNat + assets.toNat) :
    ExecStmt config frame evm accruedAssetsIteration[6]! .reverted := by
  apply ExecStmt.assignExprRevert (checkedAddSourceOverflow ?_ ?_ hbad)
  · simp only [evalExpr?, ht, EvalResult.ofOption]
  · simp only [evalExpr?, ha, EvalResult.ofOption]

theorem AccruedAssetsLocals.sum {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i total cursor : UInt256} (h : AccruedAssetsLocals v frame i total cursor)
    (assets : UInt256) :
    AccruedAssetsLocals v (accruedAssetsTotalFrame frame total assets)
      i (total + assets) cursor := by
  refine ⟨h.contract, h.imms, ?_, store_get_self _ _ _, ?_, ?_⟩ <;>
    rw [accruedAssetsTotalFrame, store_get_ne _ _ (by decide)]
  · exact h.index
  · exact h.cursor
  · exact h.queue

theorem accruedAssetsSumPreserves (frame : Frame) (total assets : UInt256) :
    AccruedAssetsPreserves frame (accruedAssetsTotalFrame frame total assets) := by
  intro key _ _ _ _ ht _
  exact store_get_ne _ _ ht

theorem AccruedAssetsLocals.post {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i total cursor : UInt256} (h : AccruedAssetsLocals v frame i total cursor) :
    AccruedAssetsLocals v (accruedAssetsPostFrame frame i) (i + ⟨1⟩) total cursor := by
  refine ⟨h.contract, h.imms, store_get_self _ _ _, ?_, ?_, ?_⟩ <;>
    rw [accruedAssetsPostFrame, store_get_ne _ _ (by decide)]
  · exact h.total
  · exact h.cursor
  · exact h.queue

theorem accruedAssetsPostPreserves (frame : Frame) (i : UInt256) :
    AccruedAssetsPreserves frame (accruedAssetsPostFrame frame i) := by
  intro key _ _ _ _ _ hi
  exact store_get_ne _ _ hi

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
