import Benchmarks.CompoundIII.Comet.CurrentIndicesSource
import Benchmarks.CompoundIII.Comet.CheckedGetter

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

def totalTransition (borrow : Bool) : TransitionDecl :=
  if borrow then totalBorrowTransition else totalSupplyTransition

def totalReadWord (v : CometWithExtendedAssetListImmutables) (w0 w1 time : UInt256)
    (borrow : Bool) : UInt256 :=
  presentValueWord (currentIndex v w0 w1 time borrow) (totalsPrincipalWord w1 borrow)

def totalReadTail (borrow : Bool) : List Stmt :=
  [.letDecl (indexLocalName borrow) (some (.elem (.int (.uint ⟨64, by decide⟩))))
      (.tupleGet (.var "__c1") (if borrow then 1 else 0)),
    .internalCall (presentValueName borrow)
      [.var (indexLocalName borrow), .storage ⟨totalsPrincipalName borrow, []⟩] "__c2",
    .return [.var "__c2"]]

theorem totalTransition_body (borrow : Bool) :
    (totalTransition borrow).body = calldataPrologue (currentIndicesBlock ++ totalReadTail borrow) := by
  cases borrow <;> rfl

theorem totalReadTail_returns (v : CometWithExtendedAssetListImmutables)
    (frame : Frame) (evm : EVM.State) (borrow : Bool) (hc : frame.contract = contract)
    (hi : frame.immutables = immStore v)
    (hp : frame.locals.get? (totalsPrincipalName borrow) = none)
    (hv : CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv)) :
    let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
    let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
    ∃ final, ExecBlock config (currentIndicesFrame frame v w0 w1 (timestampWord evm.executionEnv))
      evm (totalReadTail borrow) (.returned final evm
        (some [.int (totalReadWord v w0 w1 (timestampWord evm.executionEnv) borrow).toNat])) := by
  dsimp only
  let w0 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩
  let w1 := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩
  let time := timestampWord evm.executionEnv
  let idx := currentIndex v w0 w1 time borrow
  let f0 := currentIndicesFrame frame v w0 w1 time
  let f1 : Frame := { f0 with locals := f0.locals.insert (indexLocalName borrow) (.int idx.toNat) }
  let val := totalReadWord v w0 w1 time borrow
  let f2 : Frame := { f1 with locals := f1.locals.insert "__c2" (.int val.toNat) }
  refine ⟨f2, ?_⟩
  have htuple : evalExpr? config f0 evm
      (.tupleGet (.var "__c1") (if borrow then 1 else 0)) = .ok (.int idx.toNat) := by
    simp only [evalExpr?, f0, currentIndicesFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption, bind, EvalResult.bind]
    cases borrow <;> rfl
  apply ExecBlock.consNormal (ExecStmt.letDecl htuple)
  have he : evalExpr? config f1 evm (.var (indexLocalName borrow)) = .ok (.int idx.toNat) := by
    simp only [evalExpr?, f1, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      beq_self_eq_true, if_true, EvalResult.ofOption]
  have hfp : f1.locals.get? (totalsPrincipalName borrow) = none := by
    cases borrow <;>
      simpa only [f1, f0, currentIndicesFrame, indexLocalName, totalsPrincipalName,
        Bool.false_eq_true, if_false, if_true, Std.HashMap.get?_eq_getElem?,
        Std.HashMap.getElem?_insert] using hp
  have hep : evalExpr? config f1 evm (.storage ⟨totalsPrincipalName borrow, []⟩) =
      .ok (.int (totalsPrincipalWord w1 borrow).toNat) := by
    have hf : f1 = { contract := contract, locals := f1.locals, immutables := immStore v } := by
      simp only [f1, f0, currentIndicesFrame, hc, hi]
    rw [hf]
    exact evalTotalsPrincipal evm f1.locals (immStore v) borrow hfp
  apply ExecBlock.consNormal (presentValue_call f1 evm borrow idx (totalsPrincipalWord w1 borrow)
    _ _ "__c2" hc (currentIndex_lt hv borrow) (totalsPrincipalWord_lt _ _) he hep)
  exact ABlock.start.returns (by
    simp only [evalExpr?, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      EvalResult.ofOption]
    rfl)

theorem getTotal_returns {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hvalid : CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
      (timestampWord I)) :
    ∃ final, ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
      (totalTransition borrow).body (.returned final (initState σ σ₀ g A I)
        (some [.int (totalReadWord v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
          (timestampWord I) borrow).toNat])) (immStore v) := by
  let evm := initState σ σ₀ g A I
  let frame := calldataLocalFrame { contract := contract, locals := ∅, immutables := immStore v } evm
  have hvs : CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv) := by
    simpa only [evm, storageLoad_initState_solcSlotWord, solcSlotWordAt] using hvalid
  obtain ⟨final, hf⟩ := totalReadTail_returns v frame evm borrow rfl rfl
    (by cases borrow <;> simp [frame, calldataLocalFrame, totalsPrincipalName]) hvs
  refine ⟨final, ?_⟩
  rw [totalTransition_body]
  apply ExecFuncBody.execBlockRet
  apply (calldataPrologue_ok hv hhi).run
  have hb := currentIndicesBlock_result v frame evm rfl rfl
    (by simp [frame, calldataLocalFrame])
  dsimp only at hb
  rw [if_pos hvs] at hb
  have hfull := execBlockAppendOk hb hf
  simpa only [evm, storageLoad_initState_solcSlotWord, solcSlotWordAt] using hfull

theorem getTotal_reverts {σ σ₀ A I} {g : Sat256}
    (v : CometWithExtendedAssetListImmutables) (borrow : Bool)
    (hv : I.weiValue = ⟨0⟩) (hhi : I.calldata.size < 2^255 + 4)
    (hvalid : ¬ CurrentIndicesValid v (solcSlotWordAt ⟨0⟩ σ I) (solcSlotWordAt ⟨1⟩ σ I)
      (timestampWord I)) :
    ExecTransitionBody config contract (initState σ σ₀ g A I) ∅
      (totalTransition borrow).body .reverted (immStore v) := by
  let evm := initState σ σ₀ g A I
  let frame := calldataLocalFrame { contract := contract, locals := ∅, immutables := immStore v } evm
  rw [totalTransition_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  have hb := currentIndicesBlock_result v frame evm rfl rfl
    (by simp [frame, calldataLocalFrame])
  dsimp only at hb
  have hvs : ¬ CurrentIndicesValid v
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨0⟩)
      (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) (timestampWord evm.executionEnv) := by
    simpa only [evm, storageLoad_initState_solcSlotWord, solcSlotWordAt] using hvalid
  rw [if_neg hvs] at hb
  exact execBlockAppendReverted hb

end Benchmarks.CompoundIII.Comet
