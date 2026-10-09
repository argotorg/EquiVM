import Benchmarks.Safe.RawStorage
import Benchmarks.Safe.FallbackMemory
import Reasoning.ABIViews
import Reasoning.ExternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def fallbackArgs (cd : ByteArray) : Store := (∅ : Store).insert "calldata" (.bytes cd)

def fallbackHandler (evm : EVM.State) : UInt256 :=
  Solm.EVM.storageLoad evm evm.executionEnv.codeOwner fallbackHandlerSlot

def fallbackLocals (cd : ByteArray) (handler : UInt256) : Store :=
  ((fallbackArgs cd).insert "handlerWord" (.int (Int.ofNat handler.toNat))).insert
    "handler" (.address (AccountAddress.ofNat handler.toNat))

def fallbackCallBody : List Stmt :=
  [.lowLevelCall (.var "handler") (.intLit 0)
      (.abiEncodePacked [(bytesTy, .var "calldata"), (addr, sender)])
      "handlerSuccess" "handlerReturn",
    .require (.var "handlerSuccess"), .return [.var "handlerReturn"]]

def fallbackChoice : Stmt :=
  .ite (eqE (.var "handlerWord") (.intLit 0)) [.return [emptyBytes]] fallbackCallBody

def fallbackFinalLocals (cd : ByteArray) (handler : UInt256) (z : Bool) (out : ByteArray) :
    Store :=
  ((fallbackLocals cd handler).insert "handlerSuccess" (.bool z)).insert "handlerReturn"
    (.bytes out)

theorem safeFallbackPrefix (evm : EVM.State) {result : ExecResult}
    (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (htail : ExecBlock config
      { contract := contract, locals :=
          fallbackLocals evm.executionEnv.calldata (fallbackHandler evm) }
      evm [fallbackChoice] result) :
    ExecBlock config { contract := contract, locals := fallbackArgs evm.executionEnv.calldata }
      evm fallbackTransition.body result := by
  refine .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.letDecl ?_) (.consNormal (.letDecl ?_) htail))
  · exact safeEvalRawStorage evm _ _ fallbackHandlerSlot
      (by simp [fallbackArgs]) (by simp [evalExpr?, pure])
  · simp [uint256AsAddress, addrSt, evalExpr?, castValue?, EvalResult.ofOption,
      EvalResult.bind, bind, pure, Int.ofNat_eq_natCast]
    have hn : ¬ ((↑(fallbackHandler evm).toNat : Int) < 0) :=
      not_lt.mpr (Int.natCast_nonneg _)
    simp only [hn, if_false]

theorem safeFallbackCondition (evm : EVM.State) (cd : ByteArray) (handler : UInt256) :
    evalExpr? config { contract := contract, locals := fallbackLocals cd handler } evm
      (eqE (.var "handlerWord") (.intLit 0)) = .ok (.bool (decide (handler = ⟨0⟩))) := by
  simp [fallbackLocals, eqE, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    evalBinaryOp_eq_int_ok, Std.HashMap.getElem_insert, Std.HashMap.getElem?_insert]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq]
  constructor
  · intro h
    exact uint256_toNat_eq_zero (by omega)
  · intro h
    subst handler
    rfl

theorem safeFallbackData (evm : EVM.State) (handler : UInt256) :
    evalExpr? config
      { contract := contract, locals := fallbackLocals evm.executionEnv.calldata handler } evm
      (.abiEncodePacked [(bytesTy, .var "calldata"), (addr, sender)]) =
      .ok (.bytes (fallbackCallData evm.executionEnv.calldata evm.executionEnv.source)) := by
  simp [fallbackLocals, fallbackArgs, fallbackCallData, evalExpr?, evalPackedArgs?, sender,
    envValue,
    encodePackedValue?, bytesTy, addr, EvalResult.ofOption, EvalResult.bind, bind, pure,
    Std.HashMap.getElem_insert, Std.HashMap.getElem?_insert, ← bytearray_append_list_eq]

theorem safeFallbackZero (evm : EVM.State) (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hz : fallbackHandler evm = ⟨0⟩) :
    ExecTransitionBody config contract evm (fallbackArgs evm.executionEnv.calldata)
      fallbackTransition.body
      (.returned { contract := contract, locals :=
          fallbackLocals evm.executionEnv.calldata (fallbackHandler evm) }
        evm (some [.bytes ByteArray.empty])) := by
  apply ExecFuncBody.execBlockRet
  apply safeFallbackPrefix evm hv
  exact .consReturn (.iteTrue (by
    simpa [hz] using safeFallbackCondition evm evm.executionEnv.calldata (fallbackHandler evm))
    (.consReturn (.return (by simp [evalExprs?, evalExpr?, emptyBytes,
      EvalResult.bind, bind, pure]))))

theorem safeFallbackCallSuccess {evm evm' : EVM.State} {out : ByteArray}
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hn : fallbackHandler evm ≠ ⟨0⟩)
    (hcall : callViaEVM evm (AccountAddress.ofNat (fallbackHandler evm).toNat) 0
      (fallbackCallData evm.executionEnv.calldata evm.executionEnv.source) (true, evm', out)) :
    ExecTransitionBody config contract evm (fallbackArgs evm.executionEnv.calldata)
      fallbackTransition.body
      (.returned { contract := contract, locals :=
          fallbackFinalLocals evm.executionEnv.calldata (fallbackHandler evm) true out }
        evm' (some [.bytes out])) := by
  apply ExecFuncBody.execBlockRet
  apply safeFallbackPrefix evm hv
  refine .consReturn (.iteFalse (by
    simpa [hn] using safeFallbackCondition evm evm.executionEnv.calldata (fallbackHandler evm)) ?_)
  refine .consNormal (.lowLevelCallSuccess (sendVal := 0) ?_ (by simp [evalExpr?, pure])
    (safeFallbackData evm _) (by simpa only [addressOfAddress] using hcall))
    (.consNormal (.requireTrue ?_) (.consReturn (.return ?_)))
  · simp [fallbackLocals, evalExpr?, EvalResult.ofOption]
  · simp [evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]
  · simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]

theorem safeFallbackCallFailure {evm evm' : EVM.State} {out : ByteArray}
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hn : fallbackHandler evm ≠ ⟨0⟩)
    (hcall : callViaEVM evm (AccountAddress.ofNat (fallbackHandler evm).toNat) 0
      (fallbackCallData evm.executionEnv.calldata evm.executionEnv.source) (false, evm', out)) :
    ExecTransitionBody config contract evm (fallbackArgs evm.executionEnv.calldata)
      fallbackTransition.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  apply safeFallbackPrefix evm hv
  refine .consRevert (.iteFalse (by
    simpa [hn] using safeFallbackCondition evm evm.executionEnv.calldata (fallbackHandler evm)) ?_)
  refine .consNormal (.lowLevelCallFailure (sendVal := 0) ?_ (by simp [evalExpr?, pure])
    (safeFallbackData evm _) (by simpa only [addressOfAddress] using hcall))
    (.consRevert (.requireFalse ?_))
  · simp [fallbackLocals, evalExpr?, EvalResult.ofOption]
  · simp [evalExpr?, EvalResult.ofOption, Std.HashMap.getElem_insert]

theorem safeFallbackValueRevert (evm : EVM.State) (hv : evm.executionEnv.weiValue ≠ ⟨0⟩) :
    ExecTransitionBody config contract evm (fallbackArgs evm.executionEnv.calldata)
      fallbackTransition.body .reverted :=
  .execBlockRevert (.consRevert (.requireFalse (evalCallvalueEq_false hv)))

end Benchmarks.Safe
