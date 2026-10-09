import Benchmarks.CompoundIII.Comet.TotalSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def reservesSnapshotBlock : List Stmt :=
  [.letDecl "accruedAt" (some (.elem (.int (.uint ⟨40, by decide⟩))))
      (.storage ⟨"lastAccrualTime", []⟩),
    .letDecl "supplyPrincipal" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.storage ⟨"totalSupplyBase", []⟩),
    .letDecl "borrowPrincipal" (some (.elem (.int (.uint ⟨104, by decide⟩))))
      (.storage ⟨"totalBorrowBase", []⟩)]

def reservesElapsedExpr : Expr :=
  .inRange (.uint ⟨40, by decide⟩) (.binary .sub (.var "__c0") (.var "accruedAt"))

def reservesIndicesBlock : List Stmt :=
  [.internalCall "accruedInterestIndices" [reservesElapsedExpr] "__c1",
    .letDecl "baseSupplyIndex_" (some (.elem (.int (.uint ⟨64, by decide⟩))))
      (.tupleGet (.var "__c1") 0),
    .letDecl "baseBorrowIndex_" (some (.elem (.int (.uint ⟨64, by decide⟩))))
      (.tupleGet (.var "__c1") 1),
    .letDecl "token" (some (.elem .address)) (.immutable "baseToken")]

def reservesStartBlock : List Stmt :=
  .internalCall "getNowInternal" [] "__c0" :: reservesSnapshotBlock ++ reservesIndicesBlock

def reservesSnapshotFrame (v : CometWithExtendedAssetListImmutables) (w1 time : UInt256) : Frame :=
  { contract := contract, immutables := immStore v
    locals := ((((∅ : Store).insert "__c0" (.int time.toNat)).insert
      "accruedAt" (.int (lastAccrualWord w1).toNat)).insert
      "supplyPrincipal" (.int (totalsPrincipalWord w1 false).toNat)).insert
      "borrowPrincipal" (.int (totalsPrincipalWord w1 true).toNat) }

def reservesIndicesFrame (v : CometWithExtendedAssetListImmutables) (w0 w1 time : UInt256) : Frame :=
  { reservesSnapshotFrame v w1 time with
    locals := (reservesSnapshotFrame v w1 time).locals.insert "__c1"
      (.tuple [.int (currentIndex v w0 w1 time false).toNat,
        .int (currentIndex v w0 w1 time true).toNat]) }

def reservesReadyFrame (v : CometWithExtendedAssetListImmutables) (w0 w1 time : UInt256) : Frame :=
  { reservesIndicesFrame v w0 w1 time with
    locals := (((reservesIndicesFrame v w0 w1 time).locals.insert
      "baseSupplyIndex_" (.int (currentIndex v w0 w1 time false).toNat)).insert
      "baseBorrowIndex_" (.int (currentIndex v w0 w1 time true).toNat)).insert
      "token" (.address v.baseToken) }

theorem reservesSnapshot_result (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) :
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    let time := timestampWord evm.executionEnv
    ExecBlock config
      { contract := contract, locals := (∅ : Store).insert "__c0" (.int time.toNat),
        immutables := immStore v } evm reservesSnapshotBlock
      (.ok (reservesSnapshotFrame v w1 time) evm) := by
  dsimp only
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalLastAccrual evm _ _ (by
    simp [totalsPrincipalName])))
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalTotalsPrincipal evm _ _ false (by
    simp [totalsPrincipalName])))
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalTotalsPrincipal evm _ _ true (by
    simp [totalsPrincipalName])))
  exact ExecBlock.nil

theorem reservesIndices_result (v : CometWithExtendedAssetListImmutables) (evm : EVM.State)
    (ht : (timestampWord evm.executionEnv).toNat < 2^40) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    let time := timestampWord evm.executionEnv
    ExecBlock config (reservesSnapshotFrame v w1 time) evm reservesIndicesBlock
      (if CurrentIndicesValid v w0 w1 time then .ok (reservesReadyFrame v w0 w1 time) evm
        else .reverted) := by
  dsimp only
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let time := timestampWord evm.executionEnv
  let f := reservesSnapshotFrame v w1 time
  have he : evalExpr? config f evm (.var "__c0") = .ok (.int (Int.ofNat time.toNat)) := by
    simp only [evalExpr?, f, reservesSnapshotFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  have ha : evalExpr? config f evm (.var "accruedAt") =
      .ok (.int (Int.ofNat (lastAccrualWord w1).toNat)) := by
    simp only [evalExpr?, f, reservesSnapshotFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  by_cases hle : (lastAccrualWord w1).toNat ≤ time.toNat
  · have hd := checkedNarrowSubSourceOk ⟨40, by decide⟩ he ha ht hle
    have hdt := currentElapsed_lt ht hle
    by_cases hav : AccruedIndicesValid v w0 w1 (currentElapsed time w1)
    · rw [if_pos (show CurrentIndicesValid v w0 w1 time from ⟨ht, hle, hav⟩)]
      apply ExecBlock.consNormal
        (accruedIndices_call_ok v f evm (currentElapsed time w1) _ "__c1" rfl rfl hd hdt hav)
      apply ExecBlock.consNormal (ExecStmt.letDecl (by
        simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption, bind, EvalResult.bind]
        rfl))
      apply ExecBlock.consNormal (ExecStmt.letDecl (by
        simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
          EvalResult.ofOption, bind, EvalResult.bind]
        rfl))
      apply ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable_baseToken config contract _ evm v))
      exact ExecBlock.nil
    · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ hav h.2.2)]
      exact ExecBlock.consRevert
        (accruedIndices_call_revert v f evm (currentElapsed time w1) _ "__c1" rfl rfl hd hdt hav)
  · rw [if_neg (show ¬ CurrentIndicesValid v w0 w1 time from fun h ↦ hle h.2.1)]
    apply ExecBlock.consRevert
    apply ExecStmt.internalCallArgsRevert
    have hd := checkedNarrowSubSourceUnderflow ⟨40, by decide⟩ he ha (Nat.lt_of_not_ge hle)
    change evalExprs? config f evm [reservesElapsedExpr] = _
    simp only [evalExprs?, reservesElapsedExpr, hd, bind, EvalResult.bind]

theorem reservesStart_result (v : CometWithExtendedAssetListImmutables) (evm : EVM.State) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    let time := timestampWord evm.executionEnv
    ExecBlock config { contract := contract, locals := ∅, immutables := immStore v }
      evm reservesStartBlock
      (if CurrentIndicesValid v w0 w1 time then .ok (reservesReadyFrame v w0 w1 time) evm
        else .reverted) := by
  dsimp only
  by_cases ht : (timestampWord evm.executionEnv).toNat < 2^40
  · apply ExecBlock.consNormal (now_call_ok _ evm "__c0" rfl ht)
    exact execBlockAppendOk (reservesSnapshot_result v evm) (reservesIndices_result v evm ht)
  · rw [if_neg (show ¬ CurrentIndicesValid v _ _ _ from fun h ↦ ht h.1)]
    exact ExecBlock.consRevert (now_call_revert _ evm "__c0" rfl ht)

end Benchmarks.CompoundIII.Comet
