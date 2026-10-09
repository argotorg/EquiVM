import Benchmarks.Safe.SignatureOffsetSource
import Benchmarks.Safe.ContractSignatureCheckSource
import Benchmarks.Safe.InternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureContractInput (p : SignatureInput) (r s : UInt256) : ContractSignatureInput :=
  ⟨AccountAddress.ofUInt256 r, p.hash, p.signatures, s⟩

def signatureContractFrame (f : Frame) (r s : UInt256) : Frame :=
  signatureSet (signatureCurrentFrame f r) "contractOffset" (uint256Value s)

def signatureContractBody : List Stmt :=
  [ .assign .localVar (varRef "currentOwner")
      (uint256AsAddress (bytes32AsUint256 (.var "r"))),
    .letDecl "contractOffset" (some uint256) (bytes32AsUint256 (.var "s")),
    .require (geE (.var "contractOffset") (.var "requiredBytes")),
    .internalCall "checkContractSignature"
      [.var "currentOwner", .var "dataHash", .var "signatures", .var "contractOffset"]
      "_contractSigOk" ]

theorem SignatureCore.contractOffset {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (r s : UInt256) : SignatureCore p (signatureContractFrame f r s) :=
  (hc.current r).set _ _ (by decide)

theorem signatureContractOffsetSource {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} (hc : SignatureCore p f) :
    evalExpr? config (signatureContractFrame f r s) evm
      (geE (.var "contractOffset") (.var "requiredBytes")) =
      .ok (.bool (decide (p.requiredBytes ≤ s.toNat))) := by
  exact evalSignatureOffsetBound "contractOffset" hc (by decide)

theorem signatureContractLocals {f : Frame} {evm : EVM.State} {r s : UInt256} {old : Value}
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old) :
    ExecBlock config f evm (signatureContractBody.take 2)
      (.ok (signatureContractFrame f r s) evm) := by
  exact signatureDynamicLocals "contractOffset" hr hs ho

theorem safeInternalCheckContract {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {result : ExecResult} (hc : SignatureCore p f)
    (hbody : ExecFuncBody config (signatureContractInput p r s).frame evm
      checkContractSignatureFunction.body result) :
    ExecStmt config (signatureContractFrame f r s) evm signatureContractBody[3]!
      (internalCallResult (signatureContractFrame f r s) "_contractSigOk" result) := by
  apply internalCallFunctionResult (callee := checkContractSignatureFunction)
    (argVals := [.address (AccountAddress.ofUInt256 r), wordBytes32Value p.hash,
      .bytes p.signatures, uint256Value s]) (locals := (signatureContractInput p r s).args)
  · have hh := evalLocalValue (cfg := config) (evm := evm) (hc.contractOffset r s).hash
    have hs := evalLocalValue (cfg := config) (evm := evm) (hc.contractOffset r s).signatures
    simp [evalExprs?, hh, hs, evalExpr?, signatureContractFrame, signatureCurrentFrame,
      signatureSet, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert, hc.hash, hc.signatures,
      EvalResult.bind, EvalResult.ofOption, bind, pure]
  · rw [(hc.contractOffset r s).contract]; rfl
  · rfl
  · convert hbody using 1
    simp only [signatureContractFrame, signatureCurrentFrame, signatureSet,
      ContractSignatureInput.frame, hc.contract, hc.immutables]

theorem signatureContractSourceRejected {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {old : Value} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old) (hb : ¬p.requiredBytes ≤ s.toNat) :
    ExecBlock config f evm signatureContractBody .reverted := by
  have hp := signatureContractLocals (evm := evm) hr hs ho
  have htail : ExecBlock config (signatureContractFrame f r s) evm
      (signatureContractBody.drop 2) .reverted :=
    .consRevert (.requireFalse (by
      simpa only [hb, decide_false] using
        signatureContractOffsetSource (evm := evm) (r := r) (s := s) hc))
  simpa only [List.take_append_drop] using execBlock_append_ok hp htail

theorem signatureContractSource {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {old : Value} {result : ExecResult} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old) (hb : p.requiredBytes ≤ s.toNat)
    (hbody : ExecFuncBody config (signatureContractInput p r s).frame evm
      checkContractSignatureFunction.body result) :
    ExecBlock config f evm signatureContractBody
      (internalCallResult (signatureContractFrame f r s) "_contractSigOk" result) := by
  have hp := signatureContractLocals (evm := evm) hr hs ho
  have hg : ExecStmt config (signatureContractFrame f r s) evm
      (.require (geE (.var "contractOffset") (.var "requiredBytes")))
      (.ok (signatureContractFrame f r s) evm) := .requireTrue (by
    simpa only [hb, decide_true] using
      signatureContractOffsetSource (evm := evm) (r := r) (s := s) hc)
  have hcall := safeInternalCheckContract hc hbody
  have htail : ExecBlock config (signatureContractFrame f r s) evm
      (signatureContractBody.drop 2)
      (internalCallResult (signatureContractFrame f r s) "_contractSigOk" result) := by
    cases result with
    | returned f' evm' values => exact .consNormal hg (.consNormal hcall .nil)
    | reverted => exact .consNormal hg (.consRevert hcall)
    | staticViolation => exact .consNormal hg (.consStatic hcall)
    | ok _ _ | «break» _ _ | «continue» _ _ => cases hbody
  simpa only [List.take_append_drop] using execBlock_append_ok hp htail

end Benchmarks.Safe
