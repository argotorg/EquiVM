import Benchmarks.Midnight.Dispatch
import Benchmarks.Midnight.SettlementSetterSource
import Benchmarks.Midnight.SettlementFields
import Benchmarks.Midnight.SourceControl
import Benchmarks.Midnight.TripleDecode
import Benchmarks.Midnight.MappingMemory
import Benchmarks.Midnight.AddressDecode

/-!
# Midnight `setMarketSettlementFee(bytes32,uint256,uint256)`

Per-function proof: calldata decode facts, the EVM trace from the dispatcher arm through the
body, the Stele body evaluation, and the `…Body` theorem `Correct.lean` consumes.
Dispatcher arm entry: pc 8463; reach lemma `midnightReachSetMarketSettlementFeeBody`.
-/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 2000000

def settlementMarketArguments (id : UInt256) (index : Nat) (value : UInt256) : Store :=
  (((∅ : Store).insert "id" (wordBytes32Value id)).insert
    "index" (.int (Int.ofNat index))).insert "newSettlementFee" (.int value.toNat)

def settlementMarketAlias (evm : EVM.State) (id : UInt256) (index : Nat) (value : UInt256) : Frame :=
  let frame := calldataFrame contract (settlementMarketArguments id index value) ∅ evm
  { frame with locals :=
      frame.locals.insert "_marketState" (.storageRef (marketStateRef id) marketStateType) }

def settlementMarketFrame (evm : EVM.State) (id value : UInt256) (i : Fin 7) : Frame :=
  resumeAfterInternalCall (settlementMarketAlias evm id i.val value)
    "__c0" (some [.int (maxSettlementFeeValue i)])

def settlementMarketState (evm : EVM.State) (id value : UInt256) (i : Fin 7) : EVM.State :=
  let slot := solcMappingSlot ⟨1⟩ id + ⟨2⟩
  Stele.EVM.storageStore evm evm.executionEnv.codeOwner slot
    (setUint16Word (Stele.EVM.storageLoad evm evm.executionEnv.codeOwner slot)
      (settlementFeeQuotient value) ⟨i.val, by omega⟩)

theorem settlementMarketInputValue (evm : EVM.State) (id : UInt256) (index : Nat) (value : UInt256) :
    (settlementMarketAlias evm id index value).locals.get?
      "newSettlementFee" = some (.int value.toNat) := by
  change ((((settlementMarketArguments id index value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).insert "_marketState"
      (.storageRef (marketStateRef id) marketStateType)).get? "newSettlementFee") = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), settlementMarketArguments,
    store_get_self]

theorem settlementMarketInputIndex (evm : EVM.State) (id : UInt256) (index : Nat) (value : UInt256) :
    (settlementMarketAlias evm id index value).locals.get?
      "index" = some (.int (Int.ofNat index)) := by
  change ((((settlementMarketArguments id index value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).insert "_marketState"
      (.storageRef (marketStateRef id) marketStateType)).get? "index") = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), settlementMarketArguments,
    store_get_ne _ _ (by decide), store_get_self]

theorem settlementMarketInputId (evm : EVM.State) (id : UInt256) (index : Nat) (value : UInt256) :
    (settlementMarketAlias evm id index value).locals.get?
      "id" = some (wordBytes32Value id) := by
  change ((((settlementMarketArguments id index value).insert "__calldata"
    (.bytes evm.executionEnv.calldata)).insert "_marketState"
      (.storageRef (marketStateRef id) marketStateType)).get? "id") = _
  rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), settlementMarketArguments,
    store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]

theorem settlementMarketValueGet (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    (settlementMarketFrame evm id value i).locals.get? "newSettlementFee" =
      some (.int value.toNat) := by
  change (((settlementMarketAlias evm id i.val value).locals.insert
    "__c0" (.int (maxSettlementFeeValue i))).get? "newSettlementFee") = _
  rw [store_get_ne _ _ (by decide), settlementMarketInputValue]

theorem settlementMarketIndexGet (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    (settlementMarketFrame evm id value i).locals.get? "index" =
      some (.int (Int.ofNat i.val)) := by
  change (((settlementMarketAlias evm id i.val value).locals.insert
    "__c0" (.int (maxSettlementFeeValue i))).get? "index") = _
  rw [store_get_ne _ _ (by decide), settlementMarketInputIndex]

theorem settlementMarketIdGet (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    (settlementMarketFrame evm id value i).locals.get? "id" =
      some (wordBytes32Value id) := by
  change (((settlementMarketAlias evm id i.val value).locals.insert
    "__c0" (.int (maxSettlementFeeValue i))).get? "id") = _
  rw [store_get_ne _ _ (by decide), settlementMarketInputId]

theorem settlementMarketCapGet (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    (settlementMarketFrame evm id value i).locals.get? "__c0" =
      some (.int (maxSettlementFeeValue i)) := store_get_self _ _ _

theorem settlementMarketAuthEval (evm : EVM.State) (id : UInt256) (index : Nat) (value : UInt256) :
    evalExpr? config (settlementMarketAlias evm id index value) evm
      (roleGuard "feeSetter") = .ok (.bool (decide (roleAllowed evm ⟨10⟩))) :=
  evalRoleGuard evm "feeSetter" ⟨10⟩ rfl
    (by simp [settlementMarketAlias, calldataFrame, settlementMarketArguments]) rfl rfl

theorem settlementMarketBindAlias (evm : EVM.State) (id : UInt256) (index : Nat) (value : UInt256) :
    ABlock config evm (calldataFrame contract (settlementMarketArguments id index value) ∅ evm)
      (setMarketSettlementFeeTransition.body.drop 3) (settlementMarketAlias evm id index value)
      (setMarketSettlementFeeTransition.body.drop 4) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.letStorage ?_) h⟩
  apply resolveBytes32Mapping
  · simp [calldataFrame, settlementMarketArguments]
  · change (((settlementMarketArguments id index value).insert "__calldata"
      (.bytes evm.executionEnv.calldata)).get? "id") = _
    rw [store_get_ne _ _ (by decide), settlementMarketArguments,
      store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), store_get_self]
  · rfl

theorem settlementMarketPrefix (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hauth : roleAllowed evm ⟨10⟩) :
    ABlock config evm (settlementMarketAlias evm id i.val value)
      (setMarketSettlementFeeTransition.body.drop 4) (settlementMarketFrame evm id value i)
      (setMarketSettlementFeeTransition.body.drop 7) := by
  refine ⟨fun h ↦ ExecBlock.consNormal (ExecStmt.requireTrue ?_)
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_)
      (ExecBlock.consNormal (maxFeeCall i rfl (settlementMarketInputIndex evm id i.val value)) h))⟩
  · simpa only [decide_eq_true hauth] using settlementMarketAuthEval evm id i.val value
  · simpa only [decide_eq_true (show i.val ≤ 6 by omega)] using
      evalSettlementIndexBound (cfg := config) (evm := evm) (settlementMarketInputIndex evm id i.val value)

theorem settlementMarketGuards (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 = 0) :
    ABlock config evm (settlementMarketAlias evm id i.val value)
      (setMarketSettlementFeeTransition.body.drop 4) (settlementMarketFrame evm id value i)
      (setMarketSettlementFeeTransition.body.drop 9) := by
  refine ⟨fun h ↦ (settlementMarketPrefix evm id value i hauth).run
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_) (ExecBlock.consNormal (ExecStmt.requireTrue ?_) h))⟩
  · simpa only [decide_eq_true hbound] using evalSettlementBound (cfg := config) (evm := evm)
      (settlementMarketValueGet evm id value i) (settlementMarketCapGet evm id value i)
  · simpa only [decide_eq_true hmultiple] using evalSettlementMultiple (cfg := config) (evm := evm)
      (settlementMarketValueGet evm id value i)

theorem settlementMarketAuthReverts (evm : EVM.State) (id : UInt256) (index : Nat) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : ¬ roleAllowed evm ⟨10⟩) :
    ExecTransitionBody config contract evm (settlementMarketArguments id index value)
      setMarketSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (settlementMarketBindAlias evm id _ value).run
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hauth] using settlementMarketAuthEval evm id index value

theorem settlementMarketIndexReverts (evm : EVM.State) (id : UInt256) (index : Nat) (value : UInt256)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hindex : ¬ index ≤ 6) :
    ExecTransitionBody config contract evm (settlementMarketArguments id index value)
      setMarketSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (settlementMarketBindAlias evm id _ value).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hauth] using settlementMarketAuthEval evm id index value
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hindex] using
    evalSettlementIndexBound (cfg := config) (evm := evm) (settlementMarketInputIndex evm id index value)

theorem settlementMarketBoundReverts (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : ¬ value.toNat ≤ maxSettlementFeeValue i) :
    ExecTransitionBody config contract evm (settlementMarketArguments id i.val value)
      setMarketSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (settlementMarketBindAlias evm id _ value).run
  apply (settlementMarketPrefix evm id value i hauth).run
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hbound] using evalSettlementBound (cfg := config) (evm := evm)
    (settlementMarketValueGet evm id value i) (settlementMarketCapGet evm id value i)

theorem settlementMarketMultipleReverts (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 ≠ 0) :
    ExecTransitionBody config contract evm (settlementMarketArguments id i.val value)
      setMarketSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (settlementMarketBindAlias evm id _ value).run
  apply (settlementMarketPrefix evm id value i hauth).run
  refine ExecBlock.consNormal (ExecStmt.requireTrue ?_) ?_
  · simpa only [decide_eq_true hbound] using evalSettlementBound (cfg := config) (evm := evm)
      (settlementMarketValueGet evm id value i) (settlementMarketCapGet evm id value i)
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [decide_eq_false hmultiple] using evalSettlementMultiple (cfg := config) (evm := evm)
    (settlementMarketValueGet evm id value i)

def settlementMarketWriteFrame (evm : EVM.State) (id value : UInt256) (i : Fin 7) : Frame :=
  let frame := settlementMarketFrame evm id value i
  { frame with locals :=
      frame.locals.insert "newSettlementFeeCbp" (.int (Int.ofNat (settlementFeeQuotient value).toNat)) }

theorem settlementMarketAliasGet (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    (settlementMarketFrame evm id value i).locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := by
  change (((settlementMarketAlias evm id i.val value).locals.insert "__c0"
    (.int (maxSettlementFeeValue i))).get? "_marketState") = _
  rw [store_get_ne _ _ (by decide)]
  exact store_get_self _ _ _

theorem settlementMarketEnabledEval (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    evalExpr? config (settlementMarketFrame evm id value i) evm
      (.binary .gt (.storage { base := "_marketState", steps := [.field "tickSpacing"] }) (.intLit 0)) =
      .ok (.bool (decide (0 < (marketTickSpacing (marketFeeWord evm id)).toNat))) := by
  rw [evalExpr_binary_nonshort (by decide : BinaryOp.gt ≠ .and) (by decide : BinaryOp.gt ≠ .or)]
  rw [evalMarketAliasTickSpacing (settlementMarketAliasGet evm id value i)]
  simp [evalExpr?, bind, pure, EvalResult.bind, evalBinaryOp?]

theorem settlementMarketAssign {frame : Frame} (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hget : frame.locals.get? "_marketState" = some (.storageRef (marketStateRef id) marketStateType)) :
    assignStorageRef? config frame evm .storage
      { base := "_marketState", steps := [.field ("settlementFeeCbp" ++ toString i.val)] }
      (.int (Int.ofNat (settlementFeeQuotient value).toNat)) =
      .ok (frame, settlementMarketState evm id value i) := by
  exact assignStorageAliasField hget (settlementFeeField_type i) rfl (settlementFeeField_layout id i)
    (storageLocStore_uint16_word evm _ _ ⟨i.val, by omega⟩)

theorem settlementMarketSelect {frame : Frame} {evm : EVM.State} {result : ExecResult}
    (i : Fin 7) (hindex : frame.locals.get? "index" = some (.int (Int.ofNat i.val)))
    (hbranch : ExecStmt config frame evm
      (.assign .storage { base := "_marketState", steps :=
        [.field ("settlementFeeCbp" ++ toString i.val)] } (.var "newSettlementFeeCbp")) result) :
    ExecStmt config frame evm (setMarketSettlementFeeTransition.body[11]!) result := by
  have he (n : Nat) : evalExpr? config frame evm (.binary .eq (.var "index") (.intLit n)) =
      .ok (.bool (decide (i.val = n))) := by
    simp only [evalExpr?, hindex, EvalResult.ofOption, bind, pure, EvalResult.bind,
      evalBinaryOp?, Reasoning.VyperDispatch.value_int_beq, Int.ofNat_eq_natCast]
    norm_cast
  fin_cases i
  · apply ExecStmt.iteTrue (by simpa using he 0)
    exact execBlock_singleton hbranch
  · apply ExecStmt.iteFalse (by simpa using he 0)
    apply execBlock_singleton
    apply ExecStmt.iteTrue (by simpa using he 1)
    exact execBlock_singleton hbranch
  · apply ExecStmt.iteFalse (by simpa using he 0)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 1)
    apply execBlock_singleton
    apply ExecStmt.iteTrue (by simpa using he 2)
    exact execBlock_singleton hbranch
  · apply ExecStmt.iteFalse (by simpa using he 0)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 1)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 2)
    apply execBlock_singleton
    apply ExecStmt.iteTrue (by simpa using he 3)
    exact execBlock_singleton hbranch
  · apply ExecStmt.iteFalse (by simpa using he 0)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 1)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 2)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 3)
    apply execBlock_singleton
    apply ExecStmt.iteTrue (by simpa using he 4)
    exact execBlock_singleton hbranch
  · apply ExecStmt.iteFalse (by simpa using he 0)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 1)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 2)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 3)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 4)
    apply execBlock_singleton
    apply ExecStmt.iteTrue (by simpa using he 5)
    exact execBlock_singleton hbranch
  · apply ExecStmt.iteFalse (by simpa using he 0)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 1)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 2)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 3)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 4)
    apply execBlock_singleton
    apply ExecStmt.iteFalse (by simpa using he 5)
    apply execBlock_singleton
    apply ExecStmt.iteTrue (by simpa using he 6)
    exact execBlock_singleton hbranch

theorem settlementMarketDisabledReverts (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 = 0)
    (hspace : marketTickSpacing (marketFeeWord evm id) = ⟨0⟩) :
    ExecTransitionBody config contract evm (settlementMarketArguments id i.val value)
      setMarketSettlementFeeTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply guardedBodyBlock hwv hhi
  apply (settlementMarketBindAlias evm id i.val value).run
  apply (settlementMarketGuards evm id value i hauth hbound hmultiple).run
  apply ExecBlock.consRevert
  apply ExecStmt.requireFalse
  simpa only [hspace, show (⟨0⟩ : UInt256).toNat = 0 from rfl, Nat.lt_irrefl, decide_false]
    using settlementMarketEnabledEval evm id value i

theorem settlementMarketWritePrefix (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 = 0)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) :
    ABlock config evm (settlementMarketAlias evm id i.val value)
      (setMarketSettlementFeeTransition.body.drop 4) (settlementMarketWriteFrame evm id value i)
      (setMarketSettlementFeeTransition.body.drop 11) := by
  have hpos : 0 < (marketTickSpacing (marketFeeWord evm id)).toNat := by
    by_contra h
    exact hspace (uint256_toNat_eq_zero (by omega))
  refine ⟨fun h ↦ (settlementMarketGuards evm id value i hauth hbound hmultiple).run
    (ExecBlock.consNormal (ExecStmt.requireTrue ?_)
      (ExecBlock.consNormal (ExecStmt.letDecl
        (evalSettlementCast i (settlementMarketValueGet evm id value i) hbound)) h))⟩
  simpa only [decide_eq_true hpos] using settlementMarketEnabledEval evm id value i

theorem settlementMarketWriteIndex (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    (settlementMarketWriteFrame evm id value i).locals.get? "index" =
      some (.int (Int.ofNat i.val)) := by
  change (((settlementMarketFrame evm id value i).locals.insert "newSettlementFeeCbp"
    (.int (Int.ofNat (settlementFeeQuotient value).toNat))).get? "index") = _
  rw [store_get_ne _ _ (by decide), settlementMarketIndexGet]

theorem settlementMarketWriteAlias (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    (settlementMarketWriteFrame evm id value i).locals.get? "_marketState" =
      some (.storageRef (marketStateRef id) marketStateType) := by
  change (((settlementMarketFrame evm id value i).locals.insert "newSettlementFeeCbp"
    (.int (Int.ofNat (settlementFeeQuotient value).toNat))).get? "_marketState") = _
  rw [store_get_ne _ _ (by decide), settlementMarketAliasGet]

theorem settlementMarketWriteValueEval (evm : EVM.State) (id value : UInt256) (i : Fin 7) :
    evalExpr? config (settlementMarketWriteFrame evm id value i) evm (.var "newSettlementFeeCbp") =
      .ok (.int (Int.ofNat (settlementFeeQuotient value).toNat)) := by
  simp only [evalExpr?, settlementMarketWriteFrame, store_get_self, EvalResult.ofOption]

theorem settlementMarketReturns (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 = 0)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) (hperm : evm.executionEnv.perm = true) :
    ExecTransitionBody config contract evm (settlementMarketArguments id i.val value)
      setMarketSettlementFeeTransition.body
      (.returned (settlementMarketWriteFrame evm id value i) (settlementMarketState evm id value i) none) := by
  apply ExecFuncBody.execBlockOK
  apply guardedBodyBlock hwv hhi
  apply (settlementMarketBindAlias evm id i.val value).run
  apply (settlementMarketWritePrefix evm id value i hauth hbound hmultiple hspace).run
  apply ExecBlock.consNormal
    (settlementMarketSelect i (settlementMarketWriteIndex evm id value i)
      (ExecStmt.assign (Or.inr hperm) (settlementMarketWriteValueEval evm id value i)
        (settlementMarketAssign evm id value i (settlementMarketWriteAlias evm id value i))))
  apply ExecBlock.consNormal (ExecStmt.emit
    (vals := [wordBytes32Value id, .int (Int.ofNat i.val), .int value.toNat]) ?_ ?_) ExecBlock.nil
  · simpa only [settlementMarketState, storageStore_executionEnv] using hperm
  · have hid : (settlementMarketWriteFrame evm id value i).locals.get? "id" =
        some (wordBytes32Value id) := by
      change (((settlementMarketFrame evm id value i).locals.insert "newSettlementFeeCbp"
        (.int (Int.ofNat (settlementFeeQuotient value).toNat))).get? "id") = _
      rw [store_get_ne _ _ (by decide), settlementMarketIdGet]
    have hv : (settlementMarketWriteFrame evm id value i).locals.get? "newSettlementFee" =
        some (.int value.toNat) := by
      change (((settlementMarketFrame evm id value i).locals.insert "newSettlementFeeCbp"
        (.int (Int.ofNat (settlementFeeQuotient value).toNat))).get? "newSettlementFee") = _
      rw [store_get_ne _ _ (by decide), settlementMarketValueGet]
    simp only [evalExprs?, evalExpr?, hid, hv, settlementMarketWriteIndex,
      EvalResult.ofOption, bind, pure, EvalResult.bind]

theorem settlementMarketStatic (evm : EVM.State) (id value : UInt256) (i : Fin 7)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩) (hhi : evm.executionEnv.calldata.size < calldataLimit)
    (hauth : roleAllowed evm ⟨10⟩) (hbound : value.toNat ≤ maxSettlementFeeValue i)
    (hmultiple : value.toNat % 1000000000000 = 0)
    (hspace : marketTickSpacing (marketFeeWord evm id) ≠ ⟨0⟩) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm (settlementMarketArguments id i.val value)
      setMarketSettlementFeeTransition.body .staticViolation := by
  apply ExecFuncBody.execBlockStatic
  apply guardedBodyBlock hwv hhi
  apply (settlementMarketBindAlias evm id i.val value).run
  apply (settlementMarketWritePrefix evm id value i hauth hbound hmultiple hspace).run
  apply ExecBlock.consStatic
  exact settlementMarketSelect i (settlementMarketWriteIndex evm id value i)
    (ExecStmt.assignStatic (settlementMarketWriteValueEval evm id value i)
      (settlementMarketAssign evm id value i (settlementMarketWriteAlias evm id value i)) hperm)

def settlementMarketStorePC (i : Fin 7) : UInt256 :=
  UInt256.ofNat ([8632, 8669, 8706, 8747, 8792, 8841, 8887][i])

theorem settlementMarketStoreStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {data slot : UInt256} {R : List UInt256} (i : Fin 7)
    (hstack : R.length + 5 ≤ 1024) (hperm : I.perm = false)
    (rd : RD midnightBytecode I g s0 (settlementMarketStorePC i) (data :: slot :: R)
      mem aw rdata σ k C) : RDstatic midnightBytecode g s0 := by
  fin_cases i
  · change RD _ _ _ _ (UInt256.ofNat 8632) _ _ _ _ _ _ _ at rd
    let r0 := rd
    have r1 := r0.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
    have r2 := r1.and (by native_decide) (by evm_ov)
    have r3 := r2.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
    have r4 := r3.not (by native_decide) (by evm_ov)
    have r5 := r4.dup3 (by native_decide) (by evm_ov)
    obtain ⟨_, _, r6⟩ := RD.sload r5 (by native_decide) (by evm_ov)
    have r7 := r6.and (by native_decide) (by evm_ov)
    have r8 := r7.or (by native_decide) (by evm_ov)
    have r9 := r8.swap1 (by native_decide) (by evm_ov)
    exact r9.sstoreStatic hperm (by native_decide) (by evm_ov)
  · change RD _ _ _ _ (UInt256.ofNat 8669) _ _ _ _ _ _ _ at rd
    let r0 := rd
    have r1 := r0.dup2 (by native_decide) (by evm_ov)
    obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
    have r3 := r2.push4 (UInt256.ofNat 4294901760) (by native_decide) (by evm_ov)
    have r4 := r3.not (by native_decide) (by evm_ov)
    have r5 := r4.and (by native_decide) (by evm_ov)
    have r6 := r5.push1 (UInt256.ofNat 16) (by native_decide) (by evm_ov)
    have r7 := r6.swap2 (by native_decide) (by evm_ov)
    have r8 := r7.swap1 (by native_decide) (by evm_ov)
    have r9 := r8.swap2 (by native_decide) (by evm_ov)
    have r10 := r9.shl (by native_decide) (by evm_ov)
    have r11 := r10.push4 (UInt256.ofNat 4294901760) (by native_decide) (by evm_ov)
    have r12 := r11.and (by native_decide) (by evm_ov)
    have r13 := r12.or (by native_decide) (by evm_ov)
    have r14 := r13.swap1 (by native_decide) (by evm_ov)
    exact r14.sstoreStatic hperm (by native_decide) (by evm_ov)
  · change RD _ _ _ _ (UInt256.ofNat 8706) _ _ _ _ _ _ _ at rd
    let r0 := rd
    have r1 := r0.dup2 (by native_decide) (by evm_ov)
    obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
    have r3 := r2.pushConst (UInt256.ofNat 281470681743360) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
    have r4 := r3.not (by native_decide) (by evm_ov)
    have r5 := r4.and (by native_decide) (by evm_ov)
    have r6 := r5.push1 (UInt256.ofNat 32) (by native_decide) (by evm_ov)
    have r7 := r6.swap2 (by native_decide) (by evm_ov)
    have r8 := r7.swap1 (by native_decide) (by evm_ov)
    have r9 := r8.swap2 (by native_decide) (by evm_ov)
    have r10 := r9.shl (by native_decide) (by evm_ov)
    have r11 := r10.pushConst (UInt256.ofNat 281470681743360) (width := 6) (op := .PUSH6) (by decide) (by native_decide) (by evm_ov)
    have r12 := r11.and (by native_decide) (by evm_ov)
    have r13 := r12.or (by native_decide) (by evm_ov)
    have r14 := r13.swap1 (by native_decide) (by evm_ov)
    exact r14.sstoreStatic hperm (by native_decide) (by evm_ov)
  · change RD _ _ _ _ (UInt256.ofNat 8747) _ _ _ _ _ _ _ at rd
    let r0 := rd
    have r1 := r0.dup2 (by native_decide) (by evm_ov)
    obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
    have r3 := r2.pushConst (UInt256.ofNat 18446462598732840960) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
    have r4 := r3.not (by native_decide) (by evm_ov)
    have r5 := r4.and (by native_decide) (by evm_ov)
    have r6 := r5.push1 (UInt256.ofNat 48) (by native_decide) (by evm_ov)
    have r7 := r6.swap2 (by native_decide) (by evm_ov)
    have r8 := r7.swap1 (by native_decide) (by evm_ov)
    have r9 := r8.swap2 (by native_decide) (by evm_ov)
    have r10 := r9.shl (by native_decide) (by evm_ov)
    have r11 := r10.pushConst (UInt256.ofNat 18446462598732840960) (width := 8) (op := .PUSH8) (by decide) (by native_decide) (by evm_ov)
    have r12 := r11.and (by native_decide) (by evm_ov)
    have r13 := r12.or (by native_decide) (by evm_ov)
    have r14 := r13.swap1 (by native_decide) (by evm_ov)
    exact r14.sstoreStatic hperm (by native_decide) (by evm_ov)
  · change RD _ _ _ _ (UInt256.ofNat 8792) _ _ _ _ _ _ _ at rd
    let r0 := rd
    have r1 := r0.dup2 (by native_decide) (by evm_ov)
    obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
    have r3 := r2.pushConst (UInt256.ofNat 1208907372870555465154560) (width := 10) (op := .PUSH10) (by decide) (by native_decide) (by evm_ov)
    have r4 := r3.not (by native_decide) (by evm_ov)
    have r5 := r4.and (by native_decide) (by evm_ov)
    have r6 := r5.push1 (UInt256.ofNat 64) (by native_decide) (by evm_ov)
    have r7 := r6.swap2 (by native_decide) (by evm_ov)
    have r8 := r7.swap1 (by native_decide) (by evm_ov)
    have r9 := r8.swap2 (by native_decide) (by evm_ov)
    have r10 := r9.shl (by native_decide) (by evm_ov)
    have r11 := r10.pushConst (UInt256.ofNat 1208907372870555465154560) (width := 10) (op := .PUSH10) (by decide) (by native_decide) (by evm_ov)
    have r12 := r11.and (by native_decide) (by evm_ov)
    have r13 := r12.or (by native_decide) (by evm_ov)
    have r14 := r13.swap1 (by native_decide) (by evm_ov)
    exact r14.sstoreStatic hperm (by native_decide) (by evm_ov)
  · change RD _ _ _ _ (UInt256.ofNat 8841) _ _ _ _ _ _ _ at rd
    let r0 := rd
    have r1 := r0.dup2 (by native_decide) (by evm_ov)
    obtain ⟨_, _, r2⟩ := RD.sload r1 (by native_decide) (by evm_ov)
    have r3 := r2.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
    have r4 := r3.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
    have r5 := r4.shl (by native_decide) (by evm_ov)
    have r6 := r5.not (by native_decide) (by evm_ov)
    have r7 := r6.and (by native_decide) (by evm_ov)
    have r8 := r7.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
    have r9 := r8.swap2 (by native_decide) (by evm_ov)
    have r10 := r9.swap1 (by native_decide) (by evm_ov)
    have r11 := r10.swap2 (by native_decide) (by evm_ov)
    have r12 := r11.shl (by native_decide) (by evm_ov)
    have r13 := r12.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
    have r14 := r13.push1 (UInt256.ofNat 80) (by native_decide) (by evm_ov)
    have r15 := r14.shl (by native_decide) (by evm_ov)
    have r16 := r15.and (by native_decide) (by evm_ov)
    have r17 := r16.or (by native_decide) (by evm_ov)
    have r18 := r17.swap1 (by native_decide) (by evm_ov)
    exact r18.sstoreStatic hperm (by native_decide) (by evm_ov)
  · change RD _ _ _ _ (UInt256.ofNat 8887) _ _ _ _ _ _ _ at rd
    let r0 := rd
    have r1 := r0.jumpdest (by native_decide) (by evm_ov)
    have r2 := r1.dup2 (by native_decide) (by evm_ov)
    obtain ⟨_, _, r3⟩ := RD.sload r2 (by native_decide) (by evm_ov)
    have r4 := r3.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
    have r5 := r4.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
    have r6 := r5.shl (by native_decide) (by evm_ov)
    have r7 := r6.not (by native_decide) (by evm_ov)
    have r8 := r7.and (by native_decide) (by evm_ov)
    have r9 := r8.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
    have r10 := r9.swap2 (by native_decide) (by evm_ov)
    have r11 := r10.swap1 (by native_decide) (by evm_ov)
    have r12 := r11.swap2 (by native_decide) (by evm_ov)
    have r13 := r12.shl (by native_decide) (by evm_ov)
    have r14 := r13.push2 (UInt256.ofNat 65535) (by native_decide) (by evm_ov)
    have r15 := r14.push1 (UInt256.ofNat 96) (by native_decide) (by evm_ov)
    have r16 := r15.shl (by native_decide) (by evm_ov)
    have r17 := r16.and (by native_decide) (by evm_ov)
    have r18 := r17.or (by native_decide) (by evm_ov)
    have r19 := r18.swap1 (by native_decide) (by evm_ov)
    exact r19.sstoreStatic hperm (by native_decide) (by evm_ov)

theorem settlementMarketStoreStep {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {data slot value len topic id selector : UInt256} {R : List UInt256} (i : Fin 7)
    (hstack : R.length + 12 ≤ 1024) (hperm : I.perm = true) (hdata : data.toNat < 2 ^ 16)
    (rd : RD midnightBytecode I g s0 (settlementMarketStorePC i)
      (data :: slot :: value :: len :: topic :: id :: UInt256.ofNat i.val :: selector :: R)
      mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 ⟨8646⟩
      (value :: len :: topic :: id :: UInt256.ofNat i.val :: selector :: R) mem aw rdata
      (sstoreAccountMap I.codeOwner σ slot
        (setUint16Word (solcSlotWordAt slot σ I) data ⟨i.val, by omega⟩)) k' C' := by
  fin_cases i
  · change RD _ _ _ _ (UInt256.ofNat 8632) _ _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_8632 (by simp; omega) hperm rd
    have hc : UInt256.land (UInt256.ofNat 65535) data = data := by
      rw [u256_land_comm]
      exact u256LandMaskCleanOfToNat _ _ (by decide) hdata
    simp only [midnightBlocks.midnight_block_8632_stack, hc] at rd1
    have he := setUint16Word_clean (solcSlotWordAt slot σ I) data ⟨0, by decide⟩ hdata
    have hs : UInt256.shiftLeft data (UInt256.ofNat 0) = data := by
      apply u256_inj
      rw [shiftLeft_toNat_of_noOverflow _ _ (by decide) (by
        change data.toNat * 2 ^ 0 < UInt256.size
        simpa only [Nat.pow_zero, Nat.mul_one] using data.val.isLt)]
      change data.toNat * 1 = data.toNat
      exact Nat.mul_one _
    change setUint16Word (solcSlotWordAt slot σ I) data ⟨0, by decide⟩ =
      UInt256.lor (UInt256.land (solcSlotWordAt slot σ I) (UInt256.lnot (UInt256.ofNat 65535)))
        (UInt256.shiftLeft data (UInt256.ofNat 0)) at he
    rw [hs] at he
    simp only [solcSlotWordAt, solcSlotWord] at he
    rw [← he] at rd1
    exact ⟨_, _, rd1⟩
  · change RD _ _ _ _ (UInt256.ofNat 8669) _ _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_8669 (by simp; omega) hperm (by jump_dest) rd
    have he := setUint16Word_solc (solcSlotWordAt slot σ I) data ⟨1, by decide⟩ hdata
    change UInt256.lor
      (UInt256.land (UInt256.ofNat 4294901760) (UInt256.shiftLeft data (UInt256.ofNat 16)))
      (UInt256.land (UInt256.lnot (UInt256.ofNat 4294901760)) (solcSlotWordAt slot σ I)) =
        setUint16Word (solcSlotWordAt slot σ I) data ⟨1, by decide⟩ at he
    simp only [solcSlotWordAt, solcSlotWord] at he
    rw [he] at rd1
    exact ⟨_, _, rd1⟩
  · change RD _ _ _ _ (UInt256.ofNat 8706) _ _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_8706 (by simp; omega) hperm (by jump_dest) rd
    have he := setUint16Word_solc (solcSlotWordAt slot σ I) data ⟨2, by decide⟩ hdata
    change UInt256.lor
      (UInt256.land (UInt256.ofNat 281470681743360) (UInt256.shiftLeft data (UInt256.ofNat 32)))
      (UInt256.land (UInt256.lnot (UInt256.ofNat 281470681743360)) (solcSlotWordAt slot σ I)) =
        setUint16Word (solcSlotWordAt slot σ I) data ⟨2, by decide⟩ at he
    simp only [solcSlotWordAt, solcSlotWord] at he
    rw [he] at rd1
    exact ⟨_, _, rd1⟩
  · change RD _ _ _ _ (UInt256.ofNat 8747) _ _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_8747 (by simp; omega) hperm (by jump_dest) rd
    have he := setUint16Word_solc (solcSlotWordAt slot σ I) data ⟨3, by decide⟩ hdata
    change UInt256.lor
      (UInt256.land (UInt256.ofNat 18446462598732840960) (UInt256.shiftLeft data (UInt256.ofNat 48)))
      (UInt256.land (UInt256.lnot (UInt256.ofNat 18446462598732840960)) (solcSlotWordAt slot σ I)) =
        setUint16Word (solcSlotWordAt slot σ I) data ⟨3, by decide⟩ at he
    simp only [solcSlotWordAt, solcSlotWord] at he
    rw [he] at rd1
    exact ⟨_, _, rd1⟩
  · change RD _ _ _ _ (UInt256.ofNat 8792) _ _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_8792 (by simp; omega) hperm (by jump_dest) rd
    have he := setUint16Word_solc (solcSlotWordAt slot σ I) data ⟨4, by decide⟩ hdata
    change UInt256.lor
      (UInt256.land (UInt256.ofNat 1208907372870555465154560) (UInt256.shiftLeft data (UInt256.ofNat 64)))
      (UInt256.land (UInt256.lnot (UInt256.ofNat 1208907372870555465154560)) (solcSlotWordAt slot σ I)) =
        setUint16Word (solcSlotWordAt slot σ I) data ⟨4, by decide⟩ at he
    simp only [solcSlotWordAt, solcSlotWord] at he
    rw [he] at rd1
    exact ⟨_, _, rd1⟩
  · change RD _ _ _ _ (UInt256.ofNat 8841) _ _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_8841 (by simp; omega) hperm (by jump_dest) rd
    have he := setUint16Word_solc (solcSlotWordAt slot σ I) data ⟨5, by decide⟩ hdata
    change UInt256.lor
      (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80)) (UInt256.shiftLeft data (UInt256.ofNat 80)))
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 80))) (solcSlotWordAt slot σ I)) =
        setUint16Word (solcSlotWordAt slot σ I) data ⟨5, by decide⟩ at he
    simp only [solcSlotWordAt, solcSlotWord] at he
    rw [he] at rd1
    exact ⟨_, _, rd1⟩
  · change RD _ _ _ _ (UInt256.ofNat 8887) _ _ _ _ _ _ _ at rd
    obtain ⟨k1, C1, rd1⟩ := midnightBlocks.midnight_block_8887 (by simp; omega) hperm (by jump_dest) rd
    have he := setUint16Word_solc (solcSlotWordAt slot σ I) data ⟨6, by decide⟩ hdata
    change UInt256.lor
      (UInt256.land (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 96)) (UInt256.shiftLeft data (UInt256.ofNat 96)))
      (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 96))) (solcSlotWordAt slot σ I)) =
        setUint16Word (solcSlotWordAt slot σ I) data ⟨6, by decide⟩ at he
    simp only [solcSlotWordAt, solcSlotWord] at he
    rw [he] at rd1
    simp only [midnightBlocks.midnight_block_8887_stack] at rd1
    have rd2 := midnightBlocks.midnight_block_8880 (by simp; omega) (by jump_dest) rd1
    exact ⟨_, _, rd2⟩

theorem settlementMarketSelectTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {slot value id selector : UInt256} {R : List UInt256} (i : Fin 7)
    (hstack : R.length + 12 ≤ 1024) (hdata : (settlementFeeQuotient value).toNat < 2 ^ 16)
    (rd : RD midnightBytecode I g s0 ⟨8578⟩
      (slot :: value :: id :: UInt256.ofNat i.val :: selector :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 (settlementMarketStorePC i)
      (settlementFeeQuotient value :: slot :: value :: UInt256.ofNat 32 ::
        UInt256.ofNat 95478613538024357837750991820630627609211208098872063290803888276690345025047 ::
        id :: UInt256.ofNat i.val :: selector :: R) mem aw rdata σ k' C' := by
  have hc : UInt256.land (UInt256.ofNat 65535) (UInt256.div value (UInt256.ofNat 1000000000000)) =
      settlementFeeQuotient value := by
    rw [u256_land_comm]
    exact u256LandMaskCleanOfToNat _ _ (by decide) hdata
  fin_cases i
  · have rd1 := midnightBlocks.midnight_block_8578_fallthrough (by simp; omega) (by decide) rd
    simp only [midnightBlocks.midnight_block_8578_fallthrough_stack, hc] at rd1
    exact ⟨_, _, rd1⟩
  · have rd1 := midnightBlocks.midnight_block_8578_taken (by simp; omega) (by decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_8578_taken_stack, hc] at rd1
    have rd2 := midnightBlocks.midnight_block_8660_fallthrough (by simp; omega) (by decide) rd1
    exact ⟨_, _, rd2⟩
  · have rd1 := midnightBlocks.midnight_block_8578_taken (by simp; omega) (by decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_8578_taken_stack, hc] at rd1
    have rd2 := midnightBlocks.midnight_block_8660_taken (by simp; omega) (by decide) (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_8697_fallthrough (by simp; omega) (by decide) rd2
    exact ⟨_, _, rd3⟩
  · have rd1 := midnightBlocks.midnight_block_8578_taken (by simp; omega) (by decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_8578_taken_stack, hc] at rd1
    have rd2 := midnightBlocks.midnight_block_8660_taken (by simp; omega) (by decide) (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_8697_taken (by simp; omega) (by decide) (by jump_dest) rd2
    have rd4 := midnightBlocks.midnight_block_8738_fallthrough (by simp; omega) (by decide) rd3
    exact ⟨_, _, rd4⟩
  · have rd1 := midnightBlocks.midnight_block_8578_taken (by simp; omega) (by decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_8578_taken_stack, hc] at rd1
    have rd2 := midnightBlocks.midnight_block_8660_taken (by simp; omega) (by decide) (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_8697_taken (by simp; omega) (by decide) (by jump_dest) rd2
    have rd4 := midnightBlocks.midnight_block_8738_taken (by simp; omega) (by decide) (by jump_dest) rd3
    have rd5 := midnightBlocks.midnight_block_8783_fallthrough (by simp; omega) (by decide) rd4
    exact ⟨_, _, rd5⟩
  · have rd1 := midnightBlocks.midnight_block_8578_taken (by simp; omega) (by decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_8578_taken_stack, hc] at rd1
    have rd2 := midnightBlocks.midnight_block_8660_taken (by simp; omega) (by decide) (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_8697_taken (by simp; omega) (by decide) (by jump_dest) rd2
    have rd4 := midnightBlocks.midnight_block_8738_taken (by simp; omega) (by decide) (by jump_dest) rd3
    have rd5 := midnightBlocks.midnight_block_8783_taken (by simp; omega) (by decide) (by jump_dest) rd4
    have rd6 := midnightBlocks.midnight_block_8832_fallthrough (by simp; omega) (by decide) rd5
    exact ⟨_, _, rd6⟩
  · have rd1 := midnightBlocks.midnight_block_8578_taken (by simp; omega) (by decide) (by jump_dest) rd
    simp only [midnightBlocks.midnight_block_8578_taken_stack, hc] at rd1
    have rd2 := midnightBlocks.midnight_block_8660_taken (by simp; omega) (by decide) (by jump_dest) rd1
    have rd3 := midnightBlocks.midnight_block_8697_taken (by simp; omega) (by decide) (by jump_dest) rd2
    have rd4 := midnightBlocks.midnight_block_8738_taken (by simp; omega) (by decide) (by jump_dest) rd3
    have rd5 := midnightBlocks.midnight_block_8783_taken (by simp; omega) (by decide) (by jump_dest) rd4
    have rd6 := midnightBlocks.midnight_block_8832_taken (by simp; omega) (by decide) (by jump_dest) rd5
    have rd7 := midnightBlocks.midnight_block_8871_taken (by simp; omega) (by decide) (by jump_dest) rd6
    exact ⟨_, _, rd7⟩

theorem settlementMarketSelectWordTrace {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {slot value id index selector : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hi : index.toNat < 7)
    (hdata : (settlementFeeQuotient value).toNat < 2 ^ 16)
    (rd : RD midnightBytecode I g s0 ⟨8578⟩
      (slot :: value :: id :: index :: selector :: R) mem aw rdata σ k C) :
    ∃ k' C', RD midnightBytecode I g s0 (settlementMarketStorePC ⟨index.toNat, hi⟩)
      (settlementFeeQuotient value :: slot :: value :: UInt256.ofNat 32 ::
        UInt256.ofNat 95478613538024357837750991820630627609211208098872063290803888276690345025047 ::
        id :: UInt256.ofNat index.toNat :: selector :: R) mem aw rdata σ k' C' := by
  apply settlementMarketSelectTrace (aw := aw) (k := k) (C := C) ⟨index.toNat, hi⟩ hstack hdata
  simpa only [u256_ofNat_toNat] using rd

theorem settlementMarketTraceReturn {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {slot value id index selector : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hi : index.toNat < 7)
    (hdata : (settlementFeeQuotient value).toNat < 2 ^ 16) (hperm : I.perm = true)
    (hmem : memLoad (UInt256.ofNat 64) mem = ⟨1056⟩)
    (hzero : memLoad (UInt256.ofNat 800) (writeWord mem 1056 value) = ⟨0⟩)
    (rd : RD midnightBytecode I g s0 ⟨8578⟩
      (slot :: value :: id :: index :: selector :: R) mem aw rdata σ k C) :
    RDret midnightBytecode g s0
      (sstoreAccountMap I.codeOwner σ slot (setUint16Word (solcSlotWordAt slot σ I)
        (settlementFeeQuotient value) ⟨index.toNat, by omega⟩)) ByteArray.empty := by
  obtain ⟨k1, C1, rd1⟩ := settlementMarketSelectWordTrace hstack hi hdata rd
  obtain ⟨k2, C2, rd2⟩ := settlementMarketStoreStep ⟨index.toNat, hi⟩ hstack hperm hdata rd1
  have hr := midnightBlocks.midnight_block_8646 (by simp; omega) hperm rd2
  simp only [hmem] at hr
  change RDret _ _ _ _ ((writeWord mem 1056 value).readWithPadding
    (memLoad (UInt256.ofNat 800) (writeWord mem 1056 value)).toNat
    (memLoad (UInt256.ofNat 800) (writeWord mem 1056 value)).toNat) at hr
  simpa only [hzero, show (⟨0⟩ : UInt256).toNat = 0 from rfl,
    byteArray_readWithPadding_zero] using hr

theorem settlementMarketTraceStatic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem : ByteArray} {aw : UInt256} {rdata : ByteArray} {σ : AccountMap} {k C : Nat}
    {slot value id index selector : UInt256} {R : List UInt256}
    (hstack : R.length + 12 ≤ 1024) (hi : index.toNat < 7)
    (hdata : (settlementFeeQuotient value).toNat < 2 ^ 16) (hperm : I.perm = false)
    (rd : RD midnightBytecode I g s0 ⟨8578⟩
      (slot :: value :: id :: index :: selector :: R) mem aw rdata σ k C) :
    RDstatic midnightBytecode g s0 := by
  obtain ⟨k1, C1, rd1⟩ := settlementMarketSelectWordTrace hstack hi hdata rd
  exact settlementMarketStoreStatic ⟨index.toNat, hi⟩ (by simp; omega) hperm rd1

/-- `setMarketSettlementFee(bytes32,uint256,uint256)`: the theorem `Correct.lean` routes selector 29 to. -/
theorem midnightSetMarketSettlementFeeBody {σ σ₀ A I} {g : UInt256}
    (hcode : I.code = midnightBytecode) (hsize : I.calldata.size < UInt256.size)
    (hwf : midnightWF σ I)
    (hgas : midnightGasBound g)
    (hsel : selIs I (midnightSelBytes 29)) :
    runtimeRefinementFor config contract σ σ₀ g A I := by
  have hsz : 4 ≤ I.calldata.size := calldata_size_ge_of_selIs I (midnightSelBytes 29) rfl hsel
  have hd : dispatchMsg contract I.calldata = some setMarketSettlementFeeTransition := by
    apply midnightDispatch_setMarketSettlementFee <;>
      first | exact hsel | exact selectorNe_of_selIs hsel (by decide +kernel)
  obtain ⟨k, C, rd⟩ := midnightReachSetMarketSettlementFeeBody
    (σ := σ) (σ₀ := σ₀) (A := A) (g := Sat256.ofUInt256 g) hcode hsz hsize hsel
  by_cases hwv : I.weiValue = ⟨0⟩
  · have rd1 := midnightBlocks.midnight_block_8463_fallthrough (by simp) hwv rd
    by_cases hhi : I.calldata.size < calldataLimit
    · by_cases h100 : 100 ≤ I.calldata.size
      · have rd2 := midnightBlocks.midnight_block_8469_fallthrough (by simp)
          (entrySizeCheck_ok (bytes := 96) h100 hhi hsize) rd1
        change RD _ _ _ _ _ [solcSelectorWord I] midnightEntryMemory _ _ _ _ _ at rd2
        have hdec := midnightDecodeTriple_ok "id" "index" "newSettlementFee"
          (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) h100 hhi hsize
          (decodeBytes32Word (off := 4) (by omega))
          (decodeUint256Word (off := 36) (by omega)) (decodeUint256Word (off := 68) h100)
        by_cases hauth : solcSourceWord I = UInt256.land (solcSlotWordAt ⟨10⟩ σ I) solcAddrMask
        · obtain ⟨k3, C3, rd3⟩ := midnightBlocks.midnight_block_8481_fallthrough (by simp)
            (by rw [addressMask_computed]; exact u256_sub_eq_zero_iff_eq.mpr hauth) rd2
          simp only [midnightBlocks.midnight_block_8481_fallthrough_stack,
            midnightBlocks.midnight_block_8481_fallthrough_memory, midnightEntryMemory_zero,
            show (⟨0⟩ : UInt256).toNat = 0 from rfl,
            show (UInt256.ofNat 32).toNat = 32 from rfl, wordAt0_fold, twoWordHash_fold,
            mappingMemory_fold, mappingMemory_zero, mappingMemory_hash] at rd3
          change RD _ _ _ _ _ [solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4),
            calldataWord I.calldata 68, calldataWord I.calldata 4, calldataWord I.calldata 36,
            solcSelectorWord I] (mappingMemory (calldataWord I.calldata 4) ⟨1⟩) _ _ _ _ _ at rd3
          by_cases hi : (calldataWord I.calldata 36).toNat ≤ 6
          · have rd4 := midnightBlocks.midnight_block_8527_fallthrough (by simp) (ugt_zero hi) rd3
            have rd5 := midnightBlocks.midnight_block_8535 (by simp) (by jump_dest) rd4
            simp only [midnightBlocks.midnight_block_8535_stack] at rd5
            let i : Fin 7 := ⟨(calldataWord I.calldata 36).toNat, by omega⟩
            obtain ⟨aw6, k6, C6, rd6⟩ := midnightMaxSettlementFeeWord (by simp) (by omega)
              (mappingMemory_freePtr _ _) (by jump_dest) rd5
            have hcap : (UInt256.ofNat (maxSettlementFeeValue i)).toNat = maxSettlementFeeValue i :=
              UInt256.toNat_ofNat_of_lt (maxFeeValue_lt i)
            by_cases hbound : (calldataWord I.calldata 68).toNat ≤ maxSettlementFeeValue i
            · have rd7 := midnightBlocks.midnight_block_8543_fallthrough (by simp)
                (ugt_zero (by rw [hcap]; exact hbound)) rd6
              simp only [midnightBlocks.midnight_block_8543_fallthrough_stack] at rd7
              by_cases hmultiple : (calldataWord I.calldata 68).toNat % 1000000000000 = 0
              · have rd8 := midnightBlocks.midnight_block_8550_fallthrough (by simp)
                  ((mod_eq_zero_iff _ _ (by decide)).mpr hmultiple) rd7
                by_cases hspace : marketTickSpacing
                    (solcSlotWordAt (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I) = ⟨0⟩
                · obtain ⟨k9, C9, rd9⟩ := midnightBlocks.midnight_block_8562_taken (by simp)
                    (by
                      rw [u256_add_comm (UInt256.ofNat 2)]
                      change UInt256.isZero (marketTickSpacing (solcSlotWordAt
                        (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩) σ I)) ≠ ⟨0⟩
                      rw [hspace]; decide) (by jump_dest) rd8
                  have hr := midnightBlocks.midnight_block_1275
                    (by simp [midnightBlocks.midnight_block_8562_taken_stack]) rd9
                  exact hr.reEquivExecutionRevert hcode hd hdec
                    (settlementMarketDisabledReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                      (calldataWord I.calldata 4) (calldataWord I.calldata 68) i
                      hwv hhi hauth hbound hmultiple hspace)
                · obtain ⟨k9, C9, rd9⟩ := midnightBlocks.midnight_block_8562_fallthrough (by simp)
                    (by rw [u256_add_comm (UInt256.ofNat 2)]; exact isZero_eq_zero_of_ne hspace) rd8
                  simp only [midnightBlocks.midnight_block_8562_fallthrough_stack] at rd9
                  rw [u256_add_comm (UInt256.ofNat 2)] at rd9
                  simp only [show UInt256.ofNat 2 = (⟨2⟩ : UInt256) from rfl] at rd9
                  have hq := settlementFeeQuotient_lt (calldataWord I.calldata 68) i hbound
                  by_cases hperm : I.perm = true
                  · have hz := maxFeeMemory_writeZero
                      (mem := mappingMemory (calldataWord I.calldata 4) ⟨1⟩)
                      (by rw [mappingMemory_size]) (mappingMemory_zero _ _) (calldataWord I.calldata 68)
                    have hr := settlementMarketTraceReturn (by simp) (by omega) hq hperm
                      (maxFeeMemory_freePtr _) hz rd9
                    have hac := storageWordWrite_accounts (σ := σ)
                      (evm := initState σ σ₀ (Sat256.ofUInt256 g) A I) rfl
                      (solcMappingSlot ⟨1⟩ (calldataWord I.calldata 4) + ⟨2⟩)
                      (fun old ↦ setUint16Word old (settlementFeeQuotient (calldataWord I.calldata 68))
                        ⟨i.val, by omega⟩)
                    exact hr.reEquivExecutionGen hcode hd hdec
                      (settlementMarketReturns (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (calldataWord I.calldata 4) (calldataWord I.calldata 68) i
                        hwv hhi hauth hbound hmultiple hspace hperm) hac voidReturnEquiv
                  · have hp : I.perm = false := by
                      cases h : I.perm
                      · rfl
                      · exact False.elim (hperm h)
                    have hr := settlementMarketTraceStatic (by simp) (by omega) hq hp rd9
                    exact hr.reEquivStaticHalt hcode hd hdec
                      (settlementMarketStatic (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                        (calldataWord I.calldata 4) (calldataWord I.calldata 68) i
                        hwv hhi hauth hbound hmultiple hspace hp)
              · have rd8 := midnightBlocks.midnight_block_8550_taken (by simp)
                  (fun h ↦ hmultiple ((mod_eq_zero_iff _ _ (by decide)).mp h)) (by jump_dest) rd7
                have hr := midnightBlocks.midnight_block_8920 (by simp) rd8
                exact hr.reEquivExecutionRevert hcode hd hdec
                  (settlementMarketMultipleReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                    (calldataWord I.calldata 4) (calldataWord I.calldata 68) i
                    hwv hhi hauth hbound hmultiple)
            · have rd7 := midnightBlocks.midnight_block_8543_taken (by simp)
                (by rw [ugt_one (by rw [hcap]; exact Nat.lt_of_not_ge hbound)]; decide)
                (by jump_dest) rd6
              have hr := midnightBlocks.midnight_block_8941
                (by simp [midnightBlocks.midnight_block_8543_taken_stack]) rd7
              exact hr.reEquivExecutionRevert hcode hd hdec
                (settlementMarketBoundReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                  (calldataWord I.calldata 4) (calldataWord I.calldata 68) i hwv hhi hauth hbound)
          · have rd4 := midnightBlocks.midnight_block_8527_taken (by simp)
              (by rw [ugt_one (a := calldataWord I.calldata 36) (b := UInt256.ofNat 6)
                (Nat.lt_of_not_ge hi)]; decide) (by jump_dest) rd3
            have hr := midnightBlocks.midnight_block_8962 (by simp) rd4
            exact hr.reEquivExecutionRevert hcode hd hdec
              (settlementMarketIndexReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
                (calldataWord I.calldata 4) (calldataWord I.calldata 36).toNat
                (calldataWord I.calldata 68) hwv hhi hauth hi)
        · obtain ⟨k3, C3, rd3⟩ := midnightBlocks.midnight_block_8481_taken (by simp)
            (by rw [addressMask_computed]; exact fun h ↦ hauth (u256_sub_eq_zero_iff_eq.mp h))
            (by jump_dest) rd2
          have hr := midnightBlocks.midnight_block_8983
            (by simp [midnightBlocks.midnight_block_8481_taken_stack]) rd3
          exact hr.reEquivExecutionRevert hcode hd hdec
            (settlementMarketAuthReverts (initState σ σ₀ (Sat256.ofUInt256 g) A I)
              (calldataWord I.calldata 4) (calldataWord I.calldata 36).toNat
              (calldataWord I.calldata 68) hwv hhi hauth)
      · have rd2 := midnightBlocks.midnight_block_8469_taken (by simp)
          (by
            have hc : UInt256.slt
                (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
                (UInt256.ofNat 96) = ⟨1⟩ :=
              entrySizeCheck_short hsz (Nat.lt_of_not_ge h100) (by decide) hsize
            rw [hc]; decide) (by jump_dest) rd1
        have hr := midnightBlocks.midnight_block_712 (by simp) rd2
        exact hr.reEquivDecodingFailed hcode hd
          (midnightDecodeTriple_none_short "id" "index" "newSettlementFee"
            (.bytes abiBytes32Width) (.int (.uint ⟨256, by decide⟩)) (.int (.uint ⟨256, by decide⟩))
            hsz (Nat.lt_of_not_ge h100) hsize)
    · have rd2 := midnightBlocks.midnight_block_8469_taken (by simp)
        (by
          have hc : UInt256.slt
              (UInt256.lnot (UInt256.ofNat 3) + UInt256.ofNat I.calldata.size)
              (UInt256.ofNat 96) = ⟨1⟩ :=
            entrySizeCheck_huge (Nat.le_of_not_lt hhi) hsize (by decide)
          rw [hc]; decide) (by jump_dest) rd1
      have hr := midnightBlocks.midnight_block_712 (by simp) rd2
      exact hr.reEquivDecodingFailed hcode hd
        (midnightDecodeTriple_none_huge "id" "index" "newSettlementFee"
          (.bytes abiBytes32Width) (.int (.uint ⟨256, by decide⟩)) (.int (.uint ⟨256, by decide⟩))
          (Nat.le_of_not_lt hhi) hsize)
  · have rd1 := midnightBlocks.midnight_block_8463_taken (by simp) hwv (by jump_dest) rd
    have hr := midnightBlocks.midnight_block_712 (by simp) rd1
    cases hdec : config.externalABI.decodeCalldata? (setMarketSettlementFeeTransition.params.map Param.name)
        (transitionSignature setMarketSettlementFeeTransition).paramTypes I.calldata with
    | none => exact hr.reEquivDecodingFailed hcode hd hdec
    | some args => exact hr.reEquivExecutionRevert hcode hd hdec (bodyReverts_nonPayable hwv)

end Benchmarks.Midnight
