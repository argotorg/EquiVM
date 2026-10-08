import Benchmarks.CompoundIII.Comet.AccruedIndicesSource
import Benchmarks.CompoundIII.Comet.AccrualTime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def currentElapsed (time w1 : UInt256) : UInt256 := UInt256.sub time (lastAccrualWord w1)

abbrev CurrentIndicesValid (v : CometWithExtendedAssetListImmutables)
    (w0 w1 time : UInt256) : Prop :=
  time.toNat < 2^40 ∧ (lastAccrualWord w1).toNat ≤ time.toNat ∧
    AccruedIndicesValid v w0 w1 (currentElapsed time w1)

theorem currentElapsed_lt {time w1 : UInt256} (ht : time.toNat < 2^40)
    (hle : (lastAccrualWord w1).toNat ≤ time.toNat) :
    (currentElapsed time w1).toNat < 2^40 := by
  unfold currentElapsed
  rw [usub_toNat hle]
  omega

def currentIndex (v : CometWithExtendedAssetListImmutables) (w0 w1 time : UInt256)
    (borrow : Bool) : UInt256 := accruedIndex v w0 w1 (currentElapsed time w1) borrow

theorem currentIndex_lt {v : CometWithExtendedAssetListImmutables} {w0 w1 time : UInt256}
    (h : CurrentIndicesValid v w0 w1 time) (borrow : Bool) :
    (currentIndex v w0 w1 time borrow).toNat < 2^64 := accruedIndex_lt h.2.2 borrow

def currentIndicesBlock : List Stmt :=
  [.internalCall "getNowInternal" [] "__c0",
    .internalCall "accruedInterestIndices"
      [.inRange (.uint ⟨40, by decide⟩)
        (.binary .sub (.var "__c0") (.storage ⟨"lastAccrualTime", []⟩))] "__c1"]

def currentIndicesFrame (frame : Frame) (v : CometWithExtendedAssetListImmutables)
    (w0 w1 time : UInt256) : Frame :=
  { frame with
    locals := (frame.locals.insert "__c0" (.int time.toNat)).insert "__c1"
      (.tuple [.int (currentIndex v w0 w1 time false).toNat,
        .int (currentIndex v w0 w1 time true).toNat]) }

theorem currentIndicesBlock_result (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (hc : frame.contract = contract)
    (hi : frame.immutables = immStore v) (hl : frame.locals.get? "lastAccrualTime" = none) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    let time := timestampWord evm.executionEnv
    ExecBlock config frame evm currentIndicesBlock
      (if CurrentIndicesValid v w0 w1 time then
        .ok (currentIndicesFrame frame v w0 w1 time) evm else .reverted) := by
  dsimp only
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let time := timestampWord evm.executionEnv
  let f1 : Frame := { frame with locals := frame.locals.insert "__c0" (.int time.toNat) }
  change ExecBlock _ _ _ _ (if CurrentIndicesValid v w0 w1 time then _ else _)
  by_cases ht : time.toNat < 2^40
  · apply ExecBlock.consNormal (now_call_ok frame evm "__c0" hc ht)
    have he : evalExpr? config f1 evm (.var "__c0") = .ok (.int (Int.ofNat time.toNat)) := by
      simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
        EvalResult.ofOption]
      rfl
    have hl' : f1.locals.get? "lastAccrualTime" = none := by
      simp only [f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert]
      exact hl
    have ha : evalExpr? config f1 evm (.storage ⟨"lastAccrualTime", []⟩) =
        .ok (.int (Int.ofNat (lastAccrualWord w1).toNat)) := by
      have hf : f1 = { contract := contract, locals := f1.locals, immutables := immStore v } := by
        simp only [f1, hc, hi]
      rw [hf]
      exact evalLastAccrual evm f1.locals (immStore v) hl'
    by_cases hle : (lastAccrualWord w1).toNat ≤ time.toNat
    · have hd := checkedNarrowSubSourceOk ⟨40, by decide⟩ he ha ht hle
      have hdt := currentElapsed_lt ht hle
      by_cases hav : AccruedIndicesValid v w0 w1 (currentElapsed time w1)
      · rw [if_pos (show CurrentIndicesValid v w0 w1 time from ⟨ht, hle, hav⟩)]
        apply ExecBlock.consNormal
          (accruedIndices_call_ok v f1 evm (currentElapsed time w1) _ "__c1" hc hi hd hdt hav)
        exact ExecBlock.nil
      · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ hav h.2.2)]
        exact ExecBlock.consRevert
          (accruedIndices_call_revert v f1 evm (currentElapsed time w1) _ "__c1" hc hi hd hdt hav)
    · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ hle h.2.1)]
      apply ExecBlock.consRevert
      apply ExecStmt.internalCallArgsRevert
      have hd := checkedNarrowSubSourceUnderflow ⟨40, by decide⟩ he ha (Nat.lt_of_not_ge hle)
      change evalExprs? config f1 evm _ = _
      simp only [evalExprs?, hd, bind, EvalResult.bind]
  · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ ht h.1)]
    exact ExecBlock.consRevert (now_call_revert frame evm "__c0" hc ht)

end Benchmarks.CompoundIII.Comet
