import Benchmarks.Safe.SignatureInput
import Benchmarks.Safe.InternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

theorem safeInternalCheckNSignatures {p : SignatureInput} {caller : Frame} {evm : EVM.State}
    {executor hash signatures required : Expr} {retVar : Ident} {result : ExecResult}
    (hcontract : caller.contract = contract) (himms : caller.immutables = ∅)
    (he : evalExpr? config caller evm executor = .ok (.address p.executor))
    (hh : evalExpr? config caller evm hash = .ok (wordBytes32Value p.hash))
    (hs : evalExpr? config caller evm signatures = .ok (.bytes p.signatures))
    (hr : evalExpr? config caller evm required = .ok (uint256Value p.required))
    (hbody : ExecFuncBody config p.frame evm checkNSignaturesImplFunction.body result) :
    ExecStmt config caller evm
      (.internalCall "checkNSignaturesImpl" [executor, hash, signatures, required] retVar)
      (internalCallResult caller retVar result) := by
  apply internalCallFunctionResult (callee := checkNSignaturesImplFunction)
    (argVals := [.address p.executor, wordBytes32Value p.hash, .bytes p.signatures,
      uint256Value p.required]) (locals := p.args)
  · simp [evalExprs?, he, hh, hs, hr, EvalResult.bind, bind, pure]
  · rw [hcontract]; rfl
  · rfl
  · convert hbody using 1
    simp only [SignatureInput.frame, hcontract, himms]

end Benchmarks.Safe
