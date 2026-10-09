import Benchmarks.Safe.SignatureAddressCalldata
import Benchmarks.Safe.ModuleCallerSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeInternalCheckSignatures {p : SignatureCheckInput} {caller : Frame}
    {evm : EVM.State} {executor hash signatures : Expr} {retVar : Ident} {result : ExecResult}
    (hcontract : caller.contract = contract) (himms : caller.immutables = ∅)
    (he : evalExpr? config caller evm executor = .ok (.address p.executor))
    (hh : evalExpr? config caller evm hash = .ok (wordBytes32Value p.hash))
    (hs : evalExpr? config caller evm signatures = .ok (.bytes p.signatures))
    (hbody : ExecFuncBody config p.frame evm checkSignaturesImplFunction.body result) :
    ExecStmt config caller evm
      (.internalCall "checkSignaturesImpl" [executor, hash, signatures] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := checkSignaturesImplFunction)
    (argVals := [.address p.executor, wordBytes32Value p.hash, .bytes p.signatures])
    (locals := p.args)
  · simp [evalExprs?, he, hh, hs, EvalResult.bind, bind, pure]
  · rw [hcontract]; rfl
  · rfl
  · convert hbody using 1
    simp only [SignatureCheckInput.frame, hcontract, himms]

-- LIBRARY CANDIDATE: the nonpayable and decoded-memory checks depend only on one local.
theorem signatureCallerChecks {frame : Frame} {evm : EVM.State} {payload : ByteArray}
    {result : ExecResult} {tail : List Stmt}
    (hv : evm.executionEnv.weiValue = ⟨0⟩) (hn : payload.size ≤ 2 ^ 64 - 192)
    (hl : frame.locals["signatures"]? = some (.bytes payload))
    (ht : ExecBlock config frame evm tail result) :
    ExecBlock config frame evm (nonpayable ++ decodeMemoryBytes "signatures" ++ tail)
      result := by
  exact .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consNormal (.requireTrue (by
      exact (evalLocalBytesLengthLe (cfg := config) (evm := evm) (2 ^ 64 - 192) hl).trans
        (by congr 2; exact decide_eq_true hn))) ht)

-- LIBRARY CANDIDATE: the source rejects decoded bytes that exceed the allocation bound.
theorem signatureCallerInvalid {evm : EVM.State} {args : Store} {payload : ByteArray}
    {tail : List Stmt} (hn : ¬payload.size ≤ 2 ^ 64 - 192)
    (hl : args["signatures"]? = some (.bytes payload)) :
    ExecTransitionBody config contract evm args
      (nonpayable ++ decodeMemoryBytes "signatures" ++ tail) .reverted := by
  by_cases hv : evm.executionEnv.weiValue = ⟨0⟩
  swap
  · exact bodyReverts_nonPayable hv
  apply ExecFuncBody.execBlockRevert
  exact .consNormal (.requireTrue (evalCallvalueEq_true hv))
    (.consRevert (.requireFalse (by
      exact (evalLocalBytesLengthLe (cfg := config) (evm := evm)
        (frame := { contract := contract, locals := args }) (2 ^ 64 - 192) hl).trans
          (by congr 2; exact decide_eq_false hn))))

def signatureAddressFrame (counted : Bool) (p : SignatureCheckInput) (required : UInt256) :
    Frame :=
  { contract := contract,
    locals := signatureAddressArgs counted p.executor p.hash p.signatures required }

theorem safeCheckNSignaturesAddressSource {p : SignatureInput} {evm : EVM.State}
    {result : ExecResult} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hn : p.signatures.size ≤ 2 ^ 64 - 192)
    (hbody : ExecFuncBody config p.frame evm checkNSignaturesImplFunction.body result) :
    ExecBlock config
      (signatureAddressFrame true ⟨p.executor, p.hash, p.signatures⟩ p.required) evm
      checknsignaturesAddressBytes32BytesUint256Transition.body
      (internalCallResult
        (signatureAddressFrame true ⟨p.executor, p.hash, p.signatures⟩ p.required)
        "_checked" result) := by
  apply signatureCallerChecks hv hn
  · simp [signatureAddressFrame, signatureAddressArgs, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]
  apply execBlock_singleton
  apply safeInternalCheckNSignatures (p := p) rfl rfl
  · exact evalLocalValue (by simp [signatureAddressFrame, signatureAddressArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [signatureAddressFrame, signatureAddressArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [signatureAddressFrame, signatureAddressArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [signatureAddressFrame, signatureAddressArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact hbody

theorem safeCheckSignaturesAddressSource {p : SignatureCheckInput} {evm : EVM.State}
    {result : ExecResult} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (hn : p.signatures.size ≤ 2 ^ 64 - 192)
    (hbody : ExecFuncBody config p.frame evm checkSignaturesImplFunction.body result) :
    ExecBlock config (signatureAddressFrame false p ⟨0⟩) evm
      checksignaturesAddressBytes32BytesTransition.body
      (internalCallResult (signatureAddressFrame false p ⟨0⟩) "_checked" result) := by
  apply signatureCallerChecks hv hn
  · simp [signatureAddressFrame, signatureAddressArgs, Std.HashMap.getElem?_insert]
  apply execBlock_singleton
  apply safeInternalCheckSignatures (p := p) rfl rfl
  · exact evalLocalValue (by simp [signatureAddressFrame, signatureAddressArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [signatureAddressFrame, signatureAddressArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [signatureAddressFrame, signatureAddressArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact hbody

end Benchmarks.Safe
