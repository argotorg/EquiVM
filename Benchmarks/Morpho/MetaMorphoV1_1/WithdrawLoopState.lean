import Benchmarks.Morpho.MetaMorphoV1_1.WithdrawLoopArithmeticSource
import Benchmarks.Morpho.MetaMorphoV1_1.MarketArithmetic

/-! Loop locals and the saturating subtraction followed by the early-exit test. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory
open Benchmarks.Morpho.MetaMorphoV1_1.Immutables

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

structure WithdrawLoopLocals (v : MetaMorphoV1_1Immutables) (frame : Frame)
    (i assets cursor : UInt256) : Prop where
  contract : frame.contract = Benchmarks.Morpho.MetaMorphoV1_1.contract
  imms : frame.immutables = immStore v
  index : frame.locals.get? "i" = some (uint256Value i)
  assets : frame.locals.get? "assets" = some (uint256Value assets)
  cursor : frame.locals.get? cursorName = some (uint256Value cursor)
  queue : frame.locals.get? "withdrawQueue" = none

theorem WithdrawLoopLocals.insert {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawLoopLocals v frame i assets cursor)
    (name : Ident) (value : Value)
    (hi : (name == "i") = false) (ha : (name == "assets") = false)
    (hc : (name == cursorName) = false) (hq : (name == "withdrawQueue") = false) :
    WithdrawLoopLocals v { frame with locals := frame.locals.insert name value }
      i assets cursor := by
  refine ⟨h.contract, h.imms, ?_, ?_, ?_, ?_⟩
  · rw [store_get_ne _ _ hi]; exact h.index
  · rw [store_get_ne _ _ ha]; exact h.assets
  · rw [store_get_ne _ _ hc]; exact h.cursor
  · rw [store_get_ne _ _ hq]; exact h.queue

theorem WithdrawLoopLocals.reader {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawLoopLocals v frame i assets cursor)
    (name : Ident) (value : Value) (ptr : UInt256)
    (hi : (name == "i") = false) (ha : (name == "assets") = false)
    (hq : (name == "withdrawQueue") = false) :
    WithdrawLoopLocals v (cursorResultFrame frame name value ptr) i assets ptr := by
  refine ⟨h.contract, h.imms, ?_, ?_, cursorResultFrame_cursor _ _ _ _, ?_⟩
  · rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) hi (by decide)]; exact h.index
  · rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) ha (by decide)]; exact h.assets
  · rw [cursorResultFrame_preserves _ _ _ _ _ (by decide) hq (by decide)]; exact h.queue

theorem WithdrawLoopLocals.converted {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawLoopLocals v frame i assets cursor)
    (shares sa ss ba : UInt256) :
    WithdrawLoopLocals v (withdrawLoopConvertedFrame frame shares sa ss ba) i assets cursor := by
  have h1 := h.insert "totalSupplyAssets" (uint256Value sa)
    (by decide) (by decide) (by decide) (by decide)
  have h2 := h1.insert "totalSupplyShares" (uint256Value ss)
    (by decide) (by decide) (by decide) (by decide)
  have h3 := h2.insert "totalBorrowAssets" (uint256Value ba)
    (by decide) (by decide) (by decide) (by decide)
  exact h3.insert "__c3" (uint256Value (assetsDownWord shares sa ss))
    (by decide) (by decide) (by decide) (by decide)

theorem WithdrawLoopLocals.post {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawLoopLocals v frame i assets cursor) :
    WithdrawLoopLocals v (accruedAssetsPostFrame frame i) (i + ⟨1⟩) assets cursor := by
  refine ⟨h.contract, h.imms, store_get_self _ _ _, ?_, ?_, ?_⟩ <;>
    rw [accruedAssetsPostFrame, store_get_ne _ _ (by decide)]
  · exact h.assets
  · exact h.cursor
  · exact h.queue

def withdrawRemainingWord (assets liquid : UInt256) : UInt256 :=
  UInt256.ofNat (assets.toNat - liquid.toNat)

theorem withdrawRemainingWord_toNat (assets liquid : UInt256) :
    (withdrawRemainingWord assets liquid).toNat = assets.toNat - liquid.toNat :=
  UInt256.toNat_ofNat_of_lt (lt_of_le_of_lt (Nat.sub_le _ _) assets.val.isLt)

def withdrawLoopRemainingFrame (frame : Frame) (assets liquid : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "__c5"
      (uint256Value (withdrawRemainingWord assets liquid))).insert "assets"
        (uint256Value (withdrawRemainingWord assets liquid)) }

theorem WithdrawLoopLocals.remaining {v : MetaMorphoV1_1Immutables} {frame : Frame}
    {i assets cursor : UInt256} (h : WithdrawLoopLocals v frame i assets cursor)
    (liquid : UInt256) :
    WithdrawLoopLocals v (withdrawLoopRemainingFrame frame assets liquid)
      i (withdrawRemainingWord assets liquid) cursor := by
  refine ⟨h.contract, h.imms, ?_, store_get_self _ _ _, ?_, ?_⟩ <;>
    rw [withdrawLoopRemainingFrame, store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide)]
  · exact h.index
  · exact h.cursor
  · exact h.queue

theorem withdrawLoopBreakCondition {frame : Frame} {evm : State} {assets : UInt256}
    (ha : frame.locals.get? "assets" = some (uint256Value assets)) :
    evalExpr? config frame evm (.binary .eq (.var "assets") (.intLit 0)) =
      .ok (.bool (decide (assets = ⟨0⟩))) := by
  simp only [evalExpr?, ha, EvalResult.ofOption, uint256Value,
    bind, EvalResult.bind, evalBinaryOp?, pure, BEq.beq, Value.int.injEq]
  congr 3
  exact propext (by
    constructor
    · intro h; apply u256_inj; simpa using h
    · rintro rfl; rfl)

theorem withdrawLoopRemainingSource {frame : Frame} {evm : State} {assets liquid : UInt256}
    (hc : frame.contract = contract)
    (ha : frame.locals.get? "assets" = some (uint256Value assets))
    (hl : frame.locals.get? "__c4" = some (uint256Value liquid)) :
    ExecBlock config frame evm (withdrawLoopArithmetic.drop 7)
      (if withdrawRemainingWord assets liquid = ⟨0⟩ then
        .break (withdrawLoopRemainingFrame frame assets liquid) evm
      else .ok (withdrawLoopRemainingFrame frame assets liquid) evm) := by
  rcases frame with ⟨c, locals, imms⟩
  dsimp only at hc ha hl
  subst c
  have hw : uint256Value (withdrawRemainingWord assets liquid) =
      .int (Int.ofNat (assets.toNat - liquid.toNat)) := by
    rw [uint256Value, withdrawRemainingWord_toNat]
  have hcall := zeroFloorSubCall evm locals imms assets.toNat liquid.toNat "__c5"
    (.var "assets") (.var "__c4")
    (by simp only [evalExpr?, ha, EvalResult.ofOption, uint256Value])
    (by simp only [evalExpr?, hl, EvalResult.ofOption, uint256Value])
  rw [← hw] at hcall
  apply ExecBlock.consNormal hcall
  apply ExecBlock.consNormal
    (ExecStmt.assign (value := uint256Value (withdrawRemainingWord assets liquid)) ?_ ?_)
  · have hcond := withdrawLoopBreakCondition (evm := evm)
      (frame := withdrawLoopRemainingFrame
        { contract := contract, locals := locals, immutables := imms } assets liquid)
      (store_get_self _ _ _)
    by_cases hz : withdrawRemainingWord assets liquid = ⟨0⟩
    · rw [if_pos hz]
      simp only [hz, decide_true] at hcond
      exact ExecBlock.consBreak (ExecStmt.iteTrue hcond (ExecBlock.consBreak ExecStmt.break))
    · rw [if_neg hz]
      simp only [hz, decide_false] at hcond
      exact ExecBlock.consNormal (ExecStmt.iteFalse hcond ExecBlock.nil) ExecBlock.nil
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  · simp only [assignStorageRef?, store_get_ne _ _ (by decide : ("__c5" == "assets") = false),
      ha, updateLocalPath?, bind, EvalResult.bind, pure]
    rfl

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
