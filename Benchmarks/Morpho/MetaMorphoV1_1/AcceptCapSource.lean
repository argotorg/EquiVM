import Benchmarks.Morpho.MetaMorphoV1_1.AcceptCapStorage
import Benchmarks.Morpho.MetaMorphoV1_1.AcceptPendingSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalSyntax
import Benchmarks.Morpho.MetaMorphoV1_1.SetCapSyntax

/-! Acceptance guards and the allocated cap-setter call in the public source transition. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

def acceptCapCall : Stmt :=
  .internalCall allocatedSetCapFunction.name
    [.var "marketParams", .var "id",
      .cast (.storage ⟨"pendingCap", [.mindex (.var "id"), .field "value"]⟩)
        (.elem (.int (.uint ⟨184, by decide⟩))), .intLit 288] "__c2"

def acceptCapBody : List Stmt :=
  [.require (.binary .eq (.env .callvalue) (.intLit 0)),
    .letDecl "__calldata" (some .bytes) (.env .msgData),
    .require (.binary .lt (.arrayLength .localVar ⟨"__calldata", []⟩)
      (.intLit (Int.ofNat (2 ^ 255 + 4)))),
    .letDecl "marketParams" none marketRemovalStructExpr,
    .internalCall "MarketParamsLib_id" [.var "marketParams"] "__c0",
    .letDecl "afterTimelock_validAt" (some abiUInt256)
      (.storage ⟨"pendingCap", [.mindex (.var "__c0"), .field "validAt"]⟩),
    .require acceptPendingNonzero, .require acceptPendingTime,
    .internalCall "MarketParamsLib_id" [.var "marketParams"] "id", acceptCapCall]

theorem acceptCapBody_eq : acceptCapTransition.body = acceptCapBody := by decide +kernel

abbrev acceptCapAllowed (evm : State) (id : UInt256) : Prop :=
  marketRemovalPendingAt evm id ≠ ⟨0⟩ ∧
    (marketRemovalPendingAt evm id).toNat ≤ (UInt256.ofNat evm.executionEnv.header.timestamp).toNat

def acceptCapHashFrame (evm : State) (imms : Store) (out : ByteArray) : Frame :=
  { marketRemovalParamsFrame evm imms out with
    locals := (marketRemovalParamsFrame evm imms out).locals.insert "__c0"
      (wordBytes32Value (marketParamsData out).id) }

def acceptCapTimeFrame (evm : State) (imms : Store) (out : ByteArray) : Frame :=
  { acceptCapHashFrame evm imms out with
    locals := (acceptCapHashFrame evm imms out).locals.insert "afterTimelock_validAt"
      (uint256Value (marketRemovalPendingAt evm (marketParamsData out).id)) }

def acceptCapFrame (evm : State) (imms : Store) (out : ByteArray) : Frame :=
  { acceptCapTimeFrame evm imms out with
    locals := (acceptCapTimeFrame evm imms out).locals.insert "id"
      (wordBytes32Value (marketParamsData out).id) }

theorem acceptCapReadPrefix (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) :
    ABlock config evm
      ⟨contract, (∅ : Store).insert "marketParams" (.tuple (marketParamsFields out)), imms⟩
      acceptCapBody (acceptCapTimeFrame evm imms out) (acceptCapBody.drop 6) := by
  constructor
  intro result htail
  apply (nonpayableCalldataPrefix "__calldata" (2 ^ 255 + 4) hwv hhi).run
  apply ExecBlock.consNormal (ExecStmt.letDecl (marketRemovalStructSource evm imms out))
  refine ExecBlock.consNormal
    (marketParamsIdCall evm _ imms (marketParamsData out) "__c0" (.var "marketParams") ?_) ?_
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption]
  · apply ExecBlock.consNormal (ExecStmt.letDecl ?_) htail
    apply pendingCapTimeRead rfl
    · simp [acceptCapHashFrame, marketRemovalParamsFrame, marketRemovalCalldataFrame]
    · simp only [evalExpr?, acceptCapHashFrame, store_get_self, EvalResult.ofOption]

theorem acceptCapNonzeroSource (evm : State) (imms : Store) (out : ByteArray) :
    evalExpr? config (acceptCapTimeFrame evm imms out) evm acceptPendingNonzero =
      .ok (.bool (decide (marketRemovalPendingAt evm (marketParamsData out).id ≠ ⟨0⟩))) := by
  apply wordNeSource
  · simp only [evalExpr?, acceptCapTimeFrame, store_get_self, EvalResult.ofOption]
  · simp [evalExpr?, uint256Value, pure, UInt256.toNat]

theorem acceptCapTimeSource (evm : State) (imms : Store) (out : ByteArray) :
    evalExpr? config (acceptCapTimeFrame evm imms out) evm acceptPendingTime =
      .ok (.bool (decide ((marketRemovalPendingAt evm (marketParamsData out).id).toNat ≤
        (UInt256.ofNat evm.executionEnv.header.timestamp).toNat))) := by
  apply naturalGeSource
  · simp only [evalExpr?, envValue, pure]
  · simp only [evalExpr?, acceptCapTimeFrame, store_get_self, EvalResult.ofOption]

theorem acceptCapAllowedPrefix (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgood : acceptCapAllowed evm (marketParamsData out).id) :
    ABlock config evm
      ⟨contract, (∅ : Store).insert "marketParams" (.tuple (marketParamsFields out)), imms⟩
      acceptCapBody (acceptCapFrame evm imms out) [acceptCapCall] := by
  constructor
  intro result htail
  apply (acceptCapReadPrefix evm imms out hwv hhi).run
  apply (ABlock.start.requireStep (by
    rw [acceptCapNonzeroSource, decide_eq_true hgood.1])).run
  apply (ABlock.start.requireStep (by
    simpa only [hgood.2, decide_true] using acceptCapTimeSource evm imms out)).run
  apply ExecBlock.consNormal
    (marketParamsIdCall evm _ imms (marketParamsData out) "id" (.var "marketParams") ?_) htail
  simp [evalExpr?, acceptCapTimeFrame, acceptCapHashFrame, marketRemovalParamsFrame,
    Std.HashMap.getElem_insert, EvalResult.ofOption]

theorem acceptCapCallArgs (evm : State) (imms : Store) (out : ByteArray) :
    evalExprs? config (acceptCapFrame evm imms out) evm
      [.var "marketParams", .var "id",
        .cast (.storage ⟨"pendingCap", [.mindex (.var "id"), .field "value"]⟩)
          (.elem (.int (.uint ⟨184, by decide⟩))), .intLit 288] =
      .ok [(marketParamsData out).value, wordBytes32Value (marketParamsData out).id,
        uint256Value (acceptCapValue evm (marketParamsData out).id), uint256Value ⟨288⟩] := by
  have hi : evalExpr? config (acceptCapFrame evm imms out) evm (.var "id") =
      .ok (wordBytes32Value (marketParamsData out).id) := by
    simp only [evalExpr?, acceptCapFrame, store_get_self, EvalResult.ofOption]
  have hc := pendingCapValueCastRead rfl
    (by simp [acceptCapFrame, acceptCapTimeFrame, acceptCapHashFrame,
      marketRemovalParamsFrame, marketRemovalCalldataFrame]) hi
  have hp : evalExpr? config (acceptCapFrame evm imms out) evm (.var "marketParams") =
      .ok (marketParamsData out).value := by
    simp [evalExpr?, acceptCapFrame, acceptCapTimeFrame, acceptCapHashFrame,
      marketRemovalParamsFrame, Std.HashMap.getElem_insert, EvalResult.ofOption]
  simp only [evalExprs?, hp, hi, hc, evalExpr?, bind, EvalResult.bind, pure]
  rfl

theorem acceptCapBodyRevertsGuards (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hbad : ¬ acceptCapAllowed evm (marketParamsData out).id) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) acceptCapBody
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (acceptCapReadPrefix evm imms out hwv hhi).run
  by_cases hn : marketRemovalPendingAt evm (marketParamsData out).id ≠ ⟨0⟩
  · apply (ABlock.start.requireStep (by
      rw [acceptCapNonzeroSource, decide_eq_true hn])).run
    apply ExecBlock.consRevert (ExecStmt.requireFalse ?_)
    simpa only [show ¬ (marketRemovalPendingAt evm (marketParamsData out).id).toNat ≤
      (UInt256.ofNat evm.executionEnv.header.timestamp).toNat from fun ht ↦ hbad ⟨hn, ht⟩,
      decide_false] using acceptCapTimeSource evm imms out
  · exact ExecBlock.consRevert (ExecStmt.requireFalse (by
      simpa only [hn, decide_false] using acceptCapNonzeroSource evm imms out))

theorem acceptCapBodyCalleeRevert (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgood : acceptCapAllowed evm (marketParamsData out).id)
    (hcallee : ExecFuncBody config
      (setCapFrame imms (marketParamsData out) (marketParamsData out).id
        (acceptCapValue evm (marketParamsData out).id) ⟨288⟩)
      evm allocatedSetCapFunction.body .reverted) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) acceptCapBody
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (acceptCapAllowedPrefix evm imms out hwv hhi hgood).run
  exact ExecBlock.consRevert (internalCallFunctionRevert (callee := allocatedSetCapFunction)
    (acceptCapCallArgs evm imms out) allocatedSetCapFunction_lookup rfl hcallee)

theorem acceptCapBodyCalleeStatic (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgood : acceptCapAllowed evm (marketParamsData out).id)
    (hcallee : ExecFuncBody config
      (setCapFrame imms (marketParamsData out) (marketParamsData out).id
        (acceptCapValue evm (marketParamsData out).id) ⟨288⟩)
      evm allocatedSetCapFunction.body .staticViolation) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) acceptCapBody
      .staticViolation imms := by
  apply ExecFuncBody.execBlockStatic
  apply (acceptCapAllowedPrefix evm imms out hwv hhi hgood).run
  exact ExecBlock.consStatic (ExecStmt.internalCallStatic
    (callee := allocatedSetCapFunction.toCallable)
    (acceptCapCallArgs evm imms out) allocatedSetCapFunction_lookup rfl hcallee)

theorem acceptCapBodyCalleeReturns (evm evm' : State) (imms : Store) (out : ByteArray)
    (final : Frame) (cursor : UInt256) (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4)
    (hgood : acceptCapAllowed evm (marketParamsData out).id)
    (hcallee : ExecFuncBody config
      (setCapFrame imms (marketParamsData out) (marketParamsData out).id
        (acceptCapValue evm (marketParamsData out).id) ⟨288⟩)
      evm allocatedSetCapFunction.body (.returned final evm' (some [uint256Value cursor]))) :
    ∃ frame', ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) acceptCapBody
      (.returned frame' evm' none) imms := by
  refine ⟨resumeAfterInternalCall (acceptCapFrame evm imms out) "__c2"
    (some [uint256Value cursor]), ExecFuncBody.execBlockOK ?_⟩
  apply (acceptCapAllowedPrefix evm imms out hwv hhi hgood).run
  exact ExecBlock.consNormal (internalCallFunctionReturn (callee := allocatedSetCapFunction)
    (acceptCapCallArgs evm imms out) allocatedSetCapFunction_lookup rfl hcallee) ExecBlock.nil

end Benchmarks.Morpho.MetaMorphoV1_1
