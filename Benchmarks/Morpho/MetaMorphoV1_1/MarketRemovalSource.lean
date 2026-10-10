import Benchmarks.Morpho.MetaMorphoV1_1.MarketRemovalGuardsSource

/-! Source outcomes for market-removal scheduling: guards, overflow, storage, and static mode. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1

open SourceMemory

theorem marketRemovalTimeSource {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "timelock" = none)
    (hfit : pendingTimelockScheduleFits evm) :
    evalExpr? config frame evm marketRemovalTimeExpr =
      .ok (uint256Value (pendingTimeCastWord (pendingTimelockTime evm))) := by
  apply uint64CastSource
  apply checkedAddSourceOk (a := UInt256.ofNat evm.executionEnv.header.timestamp)
    (b := pendingTimelockDelay evm) ?_ ?_ hfit
  · simp only [evalExpr?, envValue, pure]
  · rcases frame with ⟨c, locals, imms⟩
    change c = contract at hcontract
    subst c
    exact evalStorage_timelock evm locals imms hbase

theorem marketRemovalTimeSourceRevert {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (hbase : frame.locals.get? "timelock" = none)
    (hover : ¬ pendingTimelockScheduleFits evm) :
    evalExpr? config frame evm marketRemovalTimeExpr = .revert := by
  have h := checkedAddSourceOverflow (cfg := config) (solm := frame) (evm := evm)
    (lhs := .env .timestamp) (rhs := .storage ⟨"timelock", []⟩)
    (a := UInt256.ofNat evm.executionEnv.header.timestamp) (b := pendingTimelockDelay evm)
    (by simp only [evalExpr?, envValue, pure])
    (by rcases frame with ⟨c, locals, imms⟩
        change c = contract at hcontract
        subst c
        exact evalStorage_timelock evm locals imms hbase) (Nat.le_of_not_gt hover)
  simp only [marketRemovalTimeExpr, evalExpr?, h, bind, EvalResult.bind]

@[simp] theorem marketRemovalTimeState_env (evm : State) (id time : UInt256) :
    (marketRemovalTimeState evm id time).executionEnv = evm.executionEnv :=
  storageStore_executionEnv evm _ _ _

theorem marketRemovalTailReturns {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (htime : frame.locals.get? "timelock" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfit : pendingTimelockScheduleFits evm) :
    ∃ final, ExecBlock config frame evm marketRemovalTail
      (.ok final (marketRemovalTimeState evm id (pendingTimelockTime evm))) := by
  rcases frame with ⟨c, locals, imms⟩
  change c = contract at hcontract
  subst c
  refine ⟨⟨contract, locals.insert "__c3" (.address evm.executionEnv.source), imms⟩, ?_⟩
  refine ExecBlock.consNormal (ExecStmt.assign
    (marketRemovalTimeSource rfl htime hfit)
    (assignMarketRemovalTime (pendingTimelockTime evm) rfl hconfig hid)) ?_
  refine ExecBlock.consNormal
    (internalCallReturnExpr (retTy := [.elem .address]) (expr := .env .caller)
      (value := .address evm.executionEnv.source) (by rfl)
      (by simp only [evalExpr?, envValue, marketRemovalTimeState_env, pure])) ?_
  apply (ABlock.start.emitStep (vals := [.address evm.executionEnv.source,
    wordBytes32Value id]) ?_).run
  · exact ExecBlock.nil
  · simp only [evalExprs?, evalExpr?, store_get_self,
      store_get_ne _ _ (by decide : ("__c3" == "id") = false), hid,
      EvalResult.ofOption, bind, EvalResult.bind, pure]

theorem marketRemovalTailStatic {frame : Frame} {evm : State} {id : UInt256}
    (hcontract : frame.contract = contract) (hconfig : frame.locals.get? "config" = none)
    (htime : frame.locals.get? "timelock" = none)
    (hid : frame.locals.get? "id" = some (wordBytes32Value id))
    (hfit : pendingTimelockScheduleFits evm) (hperm : evm.executionEnv.perm = false) :
    ExecBlock config frame evm marketRemovalTail .staticViolation := by
  exact ExecBlock.consStatic (execStmt_assign_static
    (ExecStmt.assign (marketRemovalTimeSource hcontract htime hfit)
      (assignMarketRemovalTime (pendingTimelockTime evm) hcontract hconfig hid)) hperm)

theorem marketRemovalTailRevert {frame : Frame} {evm : State}
    (hcontract : frame.contract = contract) (htime : frame.locals.get? "timelock" = none)
    (hover : ¬ pendingTimelockScheduleFits evm) :
    ExecBlock config frame evm marketRemovalTail .reverted :=
  ExecBlock.consRevert (ExecStmt.assignExprRevert
    (marketRemovalTimeSourceRevert hcontract htime hover))

theorem marketRemovalAllowedPrefix (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (hgood : marketRemovalAllowed evm (marketParamsData out).id) :
    ABlock config evm
      { contract := contract
        locals := (∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))
        immutables := imms }
      marketRemovalBody (marketRemovalFrame evm imms out) marketRemovalTail := by
  have hf := marketRemovalFrameReady evm imms out
  constructor
  intro result htail
  apply (marketRemovalRolePrefix evm imms out hwv hhi hrole).run
  exact (marketRemovalGuardsPass marketRemovalTail hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.2 hgood).run
    htail

theorem marketRemovalBodyReturns (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (hgood : marketRemovalAllowed evm (marketParamsData out).id)
    (hfit : pendingTimelockScheduleFits evm) :
    ∃ final, ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) marketRemovalBody
      (.returned final
        (marketRemovalTimeState evm (marketParamsData out).id (pendingTimelockTime evm)) none)
      imms := by
  have hf := marketRemovalFrameReady evm imms out
  obtain ⟨final, ht⟩ := marketRemovalTailReturns hf.1 hf.2.1 hf.2.2.2.1 hf.2.2.2.2 hfit
  exact ⟨final, ExecFuncBody.execBlockOK
    ((marketRemovalAllowedPrefix evm imms out hwv hhi hrole hgood).run ht)⟩

theorem marketRemovalBodyStatic (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (hgood : marketRemovalAllowed evm (marketParamsData out).id)
    (hfit : pendingTimelockScheduleFits evm) (hperm : evm.executionEnv.perm = false) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) marketRemovalBody
      .staticViolation imms := by
  have hf := marketRemovalFrameReady evm imms out
  exact ExecFuncBody.execBlockStatic
    ((marketRemovalAllowedPrefix evm imms out hwv hhi hrole hgood).run
      (marketRemovalTailStatic hf.1 hf.2.1 hf.2.2.2.1 hf.2.2.2.2 hfit hperm))

theorem marketRemovalBodyRevertsRole (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : ¬ curatorRoleAllowed evm) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) marketRemovalBody
      .reverted imms := by
  apply ExecFuncBody.execBlockRevert
  apply (marketRemovalPrefix evm imms out hwv hhi).run
  exact ExecBlock.consRevert (curatorRoleCallReverts evm _ imms "__role" hrole)

theorem marketRemovalBodyRevertsGuards (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (hbad : ¬ marketRemovalAllowed evm (marketParamsData out).id) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) marketRemovalBody
      .reverted imms := by
  have hf := marketRemovalFrameReady evm imms out
  apply ExecFuncBody.execBlockRevert
  apply (marketRemovalRolePrefix evm imms out hwv hhi hrole).run
  exact marketRemovalGuardsRevert marketRemovalTail hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.2 hbad

theorem marketRemovalBodyRevertsOverflow (evm : State) (imms : Store) (out : ByteArray)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hhi : evm.executionEnv.calldata.size < 2 ^ 255 + 4) (hrole : curatorRoleAllowed evm)
    (hgood : marketRemovalAllowed evm (marketParamsData out).id)
    (hover : ¬ pendingTimelockScheduleFits evm) :
    ExecTransitionBody config contract evm
      ((∅ : Store).insert "marketParams" (.tuple (marketParamsFields out))) marketRemovalBody
      .reverted imms := by
  have hf := marketRemovalFrameReady evm imms out
  exact ExecFuncBody.execBlockRevert
    ((marketRemovalAllowedPrefix evm imms out hwv hhi hrole hgood).run
      (marketRemovalTailRevert hf.1 hf.2.2.2.1 hover))

end Benchmarks.Morpho.MetaMorphoV1_1
