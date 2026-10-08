import Benchmarks.CompoundIII.Comet.PauseWrites
import Benchmarks.CompoundIII.Comet.GetterSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.CompoundIII.Comet.Immutables

namespace Benchmarks.CompoundIII.Comet

set_option maxRecDepth 10000

def PauseAuthorized (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv) : Prop :=
  I.source = v.governor ∨ I.source = v.pauseGuardian

instance (v : CometWithExtendedAssetListImmutables) (I : ExecutionEnv) :
    Decidable (PauseAuthorized v I) := inferInstanceAs (Decidable (_ ∨ _))

def pauseAuthExpr : Expr :=
  .unary .not (.binary .and
    (.binary .ne (.env .caller) (.immutable "governor"))
    (.binary .ne (.env .caller) (.immutable "pauseGuardian")))

def pauseFlagExpr : Expr :=
  let u := IntType.uint ⟨8, by decide⟩
  .binary (.bitOr u)
    (.binary (.bitOr u)
      (.binary (.bitOr u)
        (.binary (.bitOr u)
          (.binary (.bitOr u) (.cast (.intLit 0) (.elem (.int u)))
            (.binary (.shl u) (.var "__c0") (.intLit 0)))
          (.binary (.shl u) (.var "__c1") (.intLit 1)))
        (.binary (.shl u) (.var "__c2") (.intLit 2)))
      (.binary (.shl u) (.var "__c3") (.intLit 3)))
    (.binary (.shl u) (.var "__c4") (.intLit 4))

def pauseEmit : Stmt := .emit "PauseAction"
  [.var "supplyPaused", .var "transferPaused", .var "withdrawPaused", .var "absorbPaused",
    .var "buyPaused"]

def pauseWrites : List Stmt := [.assign .storage ⟨"pauseFlags", []⟩ pauseFlagExpr, pauseEmit]

theorem pause_body : pauseTransition.body = calldataPrologue
    [.require pauseAuthExpr,
      .internalCall "toUInt8" [.var "supplyPaused"] "__c0",
      .internalCall "toUInt8" [.var "transferPaused"] "__c1",
      .internalCall "toUInt8" [.var "withdrawPaused"] "__c2",
      .internalCall "toUInt8" [.var "absorbPaused"] "__c3",
      .internalCall "toUInt8" [.var "buyPaused"] "__c4",
      .assign .storage ⟨"pauseFlags", []⟩ pauseFlagExpr, pauseEmit] := rfl

theorem pauseAuth_eval (evm : EVM.State) (locals : Store)
    (v : CometWithExtendedAssetListImmutables) :
    evalExpr? config { contract := contract, locals := locals, immutables := immStore v }
      evm pauseAuthExpr = .ok (.bool (decide (PauseAuthorized v evm.executionEnv))) := by
  have hc (x y : AccountAddress) : (Value.address x == Value.address y) = decide (x = y) := by
    apply Bool.eq_iff_iff.mpr
    simp
  simp only [pauseAuthExpr, evalExpr?, evalImmutable_governor, evalImmutable_pauseGuardian,
    envValue, pure, bind, EvalResult.bind, evalBinaryOp?, evalUnaryOp?, hc]
  simp only [PauseAuthorized, Bool.decide_or]
  generalize decide (evm.executionEnv.source = v.governor) = a
  generalize decide (evm.executionEnv.source = v.pauseGuardian) = b
  cases a <;> cases b <;> rfl

def pauseReadyFrame (evm : EVM.State) (imms : Store) (a : PauseInputs) : Frame :=
  let f := calldataLocalFrame
    { contract := contract, locals := pauseInputStore a, immutables := imms } evm
  { f with locals := ((((f.locals.insert "__c0" (.int (boolWord a.supply).toNat)).insert
    "__c1" (.int (boolWord a.transfer).toNat)).insert
    "__c2" (.int (boolWord a.withdraw).toNat)).insert
    "__c3" (.int (boolWord a.absorb).toNat)).insert "__c4" (.int (boolWord a.buy).toNat) }

theorem pauseReady (evm : EVM.State) (v : CometWithExtendedAssetListImmutables)
    (a : PauseInputs) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (ha : PauseAuthorized v evm.executionEnv) :
    ABlock config evm { contract := contract, locals := pauseInputStore a, immutables := immStore v }
      pauseTransition.body (pauseReadyFrame evm (immStore v) a) pauseWrites := by
  rw [pause_body]
  refine ⟨fun h ↦ (calldataPrologue_ok hv hhi).run ?_⟩
  have hg := pauseAuth_eval evm
    ((pauseInputStore a).insert "__calldata" (.bytes evm.executionEnv.calldata)) v
  rw [decide_eq_true ha] at hg
  apply ExecBlock.consNormal (ExecStmt.requireTrue hg)
  apply ExecBlock.consNormal (toUInt8_call _ evm _ "__c0" a.supply rfl (by
    simp only [evalExpr?, pauseInputStore, calldataLocalFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl))
  apply ExecBlock.consNormal (toUInt8_call _ evm _ "__c1" a.transfer rfl (by
    simp only [evalExpr?, pauseInputStore, calldataLocalFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl))
  apply ExecBlock.consNormal (toUInt8_call _ evm _ "__c2" a.withdraw rfl (by
    simp only [evalExpr?, pauseInputStore, calldataLocalFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl))
  apply ExecBlock.consNormal (toUInt8_call _ evm _ "__c3" a.absorb rfl (by
    simp only [evalExpr?, pauseInputStore, calldataLocalFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl))
  exact ExecBlock.consNormal (toUInt8_call _ evm _ "__c4" a.buy rfl (by
    simp only [evalExpr?, pauseInputStore, calldataLocalFrame, Std.HashMap.get?_eq_getElem?,
      Std.HashMap.getElem?_insert, EvalResult.ofOption]
    rfl)) h

theorem pauseFlags_eval (evm : EVM.State) (imms : Store) (a : PauseInputs) :
    evalExpr? config (pauseReadyFrame evm imms a) evm pauseFlagExpr =
      .ok (.int (pauseFlagWord a).toNat) := by
  simp only [pauseFlagExpr, evalExpr?, pauseReadyFrame, calldataLocalFrame,
    Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert, EvalResult.ofOption]
  rcases a with ⟨s, t, w, a, b⟩
  cases s <;> cases t <;> cases w <;> cases a <;> cases b <;> rfl

theorem pauseFlagsAssign (evm : EVM.State) (imms : Store) (a : PauseInputs) :
    ExecStmt config (pauseReadyFrame evm imms a) evm
      (.assign .storage ⟨"pauseFlags", []⟩ pauseFlagExpr)
      (.ok (pauseReadyFrame evm imms a) (pauseSourceState evm a)) := by
  exact ExecStmt.assign (pauseFlags_eval evm imms a)
    (assignPauseFlags evm _ imms a (by simp [pauseReadyFrame, calldataLocalFrame, pauseInputStore]))

theorem pause_returns (evm : EVM.State) (v : CometWithExtendedAssetListImmutables)
    (a : PauseInputs) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (ha : PauseAuthorized v evm.executionEnv) :
    ExecTransitionBody config contract evm (pauseInputStore a) pauseTransition.body
      (.returned (pauseReadyFrame evm (immStore v) a) (pauseSourceState evm a) none)
      (immStore v) := by
  apply ExecFuncBody.execBlockOK
  apply (pauseReady evm v a hv hhi ha).run
  apply ExecBlock.consNormal (pauseFlagsAssign evm (immStore v) a)
  apply ExecBlock.consNormal (ExecStmt.emit (vals :=
    [.bool a.supply, .bool a.transfer, .bool a.withdraw, .bool a.absorb, .bool a.buy]) ?_)
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, pauseReadyFrame, calldataLocalFrame,
      pauseInputStore, Std.HashMap.get?_eq_getElem?, Std.HashMap.getElem?_insert,
      pure, bind, EvalResult.bind, EvalResult.ofOption]
    rfl

theorem pause_static (evm : EVM.State) (v : CometWithExtendedAssetListImmutables)
    (a : PauseInputs) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (ha : PauseAuthorized v evm.executionEnv) (hp : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (pauseInputStore a) pauseTransition.body
      .staticViolation (immStore v) := by
  apply ExecFuncBody.execBlockStatic
  apply (pauseReady evm v a hv hhi ha).run
  exact ExecBlock.consStatic (execStmt_assign_static (pauseFlagsAssign evm (immStore v) a) hp)

theorem pause_reverts (evm : EVM.State) (v : CometWithExtendedAssetListImmutables)
    (a : PauseInputs) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2^255 + 4)
    (ha : ¬ PauseAuthorized v evm.executionEnv) :
    ExecTransitionBody config contract evm (pauseInputStore a) pauseTransition.body
      .reverted (immStore v) := by
  rw [pause_body]
  apply ExecFuncBody.execBlockRevert
  apply (calldataPrologue_ok hv hhi).run
  have hg := pauseAuth_eval evm
    ((pauseInputStore a).insert "__calldata" (.bytes evm.executionEnv.calldata)) v
  rw [decide_eq_false ha] at hg
  exact ExecBlock.consRevert (ExecStmt.requireFalse hg)

end Benchmarks.CompoundIII.Comet
