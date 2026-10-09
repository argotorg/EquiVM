import Benchmarks.Safe.SignatureCallerSource
import Benchmarks.Safe.SignatureLegacyCalldata

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

def signatureLegacyFrame (counted : Bool) (hash : UInt256) (data signatures : ByteArray)
    (required : UInt256) : Frame :=
  { contract := contract, locals := signatureLegacyArgs counted hash data signatures required }

theorem safeCheckNSignaturesLegacySource {p : SignatureInput} {evm : EVM.State}
    (data : ByteArray) {result : ExecResult} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (he : p.executor = evm.executionEnv.source) (hn : p.signatures.size ≤ 2 ^ 64 - 192)
    (hbody : ExecFuncBody config p.frame evm checkNSignaturesImplFunction.body result) :
    ExecBlock config (signatureLegacyFrame true p.hash data p.signatures p.required) evm
      checknsignaturesTransition.body
      (internalCallResult (signatureLegacyFrame true p.hash data p.signatures p.required)
        "_checked" result) := by
  apply signatureCallerChecks hv hn
  · simp [signatureLegacyFrame, signatureLegacyArgs, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]
  apply execBlock_singleton
  apply safeInternalCheckNSignatures (p := p) rfl rfl
  · rw [he]; simp only [sender, evalExpr?, envValue, pure]
  · exact evalLocalValue (by simp [signatureLegacyFrame, signatureLegacyArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [signatureLegacyFrame, signatureLegacyArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [signatureLegacyFrame, signatureLegacyArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact hbody

theorem safeCheckSignaturesLegacySource {p : SignatureCheckInput} {evm : EVM.State}
    (data : ByteArray) {result : ExecResult} (hv : evm.executionEnv.weiValue = ⟨0⟩)
    (he : p.executor = evm.executionEnv.source) (hn : p.signatures.size ≤ 2 ^ 64 - 192)
    (hbody : ExecFuncBody config p.frame evm checkSignaturesImplFunction.body result) :
    ExecBlock config (signatureLegacyFrame false p.hash data p.signatures ⟨0⟩) evm
      checksignaturesTransition.body
      (internalCallResult (signatureLegacyFrame false p.hash data p.signatures ⟨0⟩)
        "_checked" result) := by
  apply signatureCallerChecks hv hn
  · simp [signatureLegacyFrame, signatureLegacyArgs, Std.HashMap.getElem?_insert]
  apply execBlock_singleton
  apply safeInternalCheckSignatures (p := p) rfl rfl
  · rw [he]; simp only [sender, evalExpr?, envValue, pure]
  · exact evalLocalValue (by simp [signatureLegacyFrame, signatureLegacyArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [signatureLegacyFrame, signatureLegacyArgs,
      Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
  · exact hbody

end Benchmarks.Safe
