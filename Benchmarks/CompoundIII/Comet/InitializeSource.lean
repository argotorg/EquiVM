import Benchmarks.CompoundIII.Comet.InitializeState
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

def initializeGuard : Expr := .binary .eq (.storage ⟨"lastAccrualTime", []⟩) (.intLit 0)

def initializeWrites : List Stmt :=
  [.assign .storage ⟨"lastAccrualTime", []⟩ (.var "__c0"),
    .assign .storage ⟨"baseSupplyIndex", []⟩ (.intLit 1000000000000000),
    .assign .storage ⟨"baseBorrowIndex", []⟩ (.intLit 1000000000000000)]

theorem initializeStorage_body : initializeStorageTransition.body = calldataPrologue
    (.require initializeGuard :: .internalCall "getNowInternal" [] "__c0" :: initializeWrites) := rfl

def initializeReadyFrame (evm : EVM.State) (imms : Store) : Frame :=
  let f := calldataLocalFrame { contract := contract, locals := ∅, immutables := imms } evm
  { f with locals := f.locals.insert "__c0" (.int (timestampWord evm.executionEnv).toNat) }

theorem initializeGuard_eval (evm : EVM.State) (locals imms : Store)
    (hlocal : locals.get? "lastAccrualTime" = none) :
    evalExpr? config { contract := contract, locals := locals, immutables := imms } evm
      initializeGuard = .ok (.bool (decide
        (lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) = ⟨0⟩))) := by
  have he := evalLastAccrual evm locals imms hlocal
  let w := lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩)
  have hbeq : (Value.int (Int.ofNat w.toNat) == Value.int 0) = decide (w = ⟨0⟩) := by
    by_cases hz : w = ⟨0⟩
    · rw [hz]
      rfl
    · rw [decide_eq_false hz]
      apply valueInt_beq_false_of_ne
      intro hh
      exact hz (uint256_toNat_eq_zero (Int.ofNat.inj hh))
  simp only [initializeGuard, evalExpr?, he, pure, bind, EvalResult.bind,
    evalBinaryOp_eq_int_ok]
  exact congrArg (fun b ↦ EvalResult.ok (Value.bool b)) hbeq

theorem initializeReady (evm : EVM.State) (imms : Store)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (hz : lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) = ⟨0⟩)
    (ht : (timestampWord evm.executionEnv).toNat < 2^40) :
    ABlock config evm { contract := contract, locals := ∅, immutables := imms }
      initializeStorageTransition.body (initializeReadyFrame evm imms) initializeWrites := by
  rw [initializeStorage_body]
  refine ⟨fun h ↦ (calldataPrologue_ok hv hhi).run ?_⟩
  have hg := initializeGuard_eval evm
    ((∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata)) imms (by simp)
  rw [decide_eq_true hz] at hg
  exact ExecBlock.consNormal (ExecStmt.requireTrue hg)
    (ExecBlock.consNormal (now_call_ok _ evm "__c0" rfl ht) h)

theorem initializeTimeAssign (evm : EVM.State) (imms : Store) :
    ExecStmt config (initializeReadyFrame evm imms) evm
      (.assign .storage ⟨"lastAccrualTime", []⟩ (.var "__c0"))
      (.ok (initializeReadyFrame evm imms) (storeLastAccrual evm (timestampWord evm.executionEnv))) := by
  apply ExecStmt.assign
  · simp only [evalExpr?, initializeReadyFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl
  · exact assignLastAccrual evm _ imms _ (by simp [initializeReadyFrame, calldataLocalFrame])

theorem initializeStorage_returns (evm : EVM.State) (imms : Store)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (hz : lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) = ⟨0⟩)
    (ht : (timestampWord evm.executionEnv).toNat < 2^40) :
    ExecTransitionBody config contract evm ∅ initializeStorageTransition.body
      (.returned (initializeReadyFrame evm imms) (initializeSourceState evm) none) imms := by
  apply ExecFuncBody.execBlockOK
  apply (initializeReady evm imms hv hhi hz ht).run
  apply ExecBlock.consNormal (initializeTimeAssign evm imms)
  have hs (state : EVM.State) (b : Bool) :
      ExecStmt config (initializeReadyFrame evm imms) state
        (.assign .storage ⟨totalsIndexName b, []⟩ (.intLit 1000000000000000))
        (.ok (initializeReadyFrame evm imms) (storeTotalsIndex state b ⟨1000000000000000⟩)) := by
    apply ExecStmt.assign (value := .int (Int.ofNat (⟨1000000000000000⟩ : UInt256).toNat))
      (by norm_num [evalExpr?, pure, UInt256.toNat, UInt256.size])
    exact assignTotalsIndex state _ imms b _ (by
      cases b <;> simp [initializeReadyFrame, calldataLocalFrame, totalsIndexName])
  exact ExecBlock.consNormal (hs _ false) (ExecBlock.consNormal (hs _ true) ExecBlock.nil)

theorem initializeStorage_static (evm : EVM.State) (imms : Store)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (hz : lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) = ⟨0⟩)
    (ht : (timestampWord evm.executionEnv).toNat < 2^40)
    (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm ∅ initializeStorageTransition.body .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (initializeReady evm imms hv hhi hz ht).run
  exact ExecBlock.consStatic (execStmt_assign_static (initializeTimeAssign evm imms) hperm)

theorem initializeStorage_reverts (evm : EVM.State) (imms : Store)
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (hinvalid : ¬ (lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) = ⟨0⟩ ∧
      (timestampWord evm.executionEnv).toNat < 2^40)) :
    ExecTransitionBody config contract evm ∅ initializeStorageTransition.body .reverted imms := by
  rw [initializeStorage_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  have hg := initializeGuard_eval evm
    ((∅ : Store).insert "__calldata" (.bytes evm.executionEnv.calldata)) imms (by simp)
  by_cases hz : lastAccrualWord (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨1⟩) = ⟨0⟩
  · rw [decide_eq_true hz] at hg
    apply ExecBlock.consNormal (ExecStmt.requireTrue hg)
    exact ExecBlock.consRevert (now_call_revert _ evm "__c0" rfl (fun ht ↦ hinvalid ⟨hz, ht⟩))
  · rw [decide_eq_false hz] at hg
    exact ExecBlock.consRevert (ExecStmt.requireFalse hg)

end Benchmarks.CompoundIII.Comet
