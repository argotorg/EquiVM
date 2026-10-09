import Benchmarks.Safe.SignatureBranchSource
import Benchmarks.Safe.EcrecoverSource
import Benchmarks.Safe.InternalCall

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000

def signatureRecoverBody (digest v : Expr) : List Stmt :=
  [ .internalCall "ecrecoverAddress" [digest, v, .var "r", .var "s"] "recoveredOwner",
    .assign .localVar (varRef "currentOwner") (.var "recoveredOwner") ]

def signatureRecoveredFrame (f : Frame) (owner : UInt256) : Frame :=
  signatureCurrentFrame
    (signatureSet f "recoveredOwner" (.address (AccountAddress.ofUInt256 owner))) owner

theorem safeInternalEcrecover {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {input : EcrecoverInput} {digest v : Expr} {result : ExecResult}
    (hc : SignatureCore p f)
    (hd : evalExpr? config f evm digest = .ok (wordBytes32Value input.digest))
    (hv : evalExpr? config f evm v = .ok (uint256Value input.v))
    (hr : f.locals["r"]? = some (wordBytes32Value input.r))
    (hs : f.locals["s"]? = some (wordBytes32Value input.s))
    (hbody : ExecFuncBody config (ecrecoverFrame input) evm ecrecoverAddressFunction.body result) :
    ExecStmt config f evm (signatureRecoverBody digest v)[0]!
      (internalCallResult f "recoveredOwner" result) := by
  apply internalCallFunctionResult (callee := ecrecoverAddressFunction)
    (argVals := [wordBytes32Value input.digest, uint256Value input.v,
      wordBytes32Value input.r, wordBytes32Value input.s]) (locals := ecrecoverArgs input)
  · simp [evalExprs?, hd, hv, evalLocalValue hr, evalLocalValue hs,
      EvalResult.bind, bind, pure]
  · rw [hc.contract]; rfl
  · rfl
  · convert hbody using 1
    simp only [ecrecoverFrame, hc.contract, hc.immutables]

theorem signatureRecoverSource {p : SignatureInput} {f : Frame} {evm evm' : EVM.State}
    {input : EcrecoverInput} {digest v : Expr} {old : Value} {owner : UInt256} {f' : Frame}
    (hc : SignatureCore p f)
    (hd : evalExpr? config f evm digest = .ok (wordBytes32Value input.digest))
    (hv : evalExpr? config f evm v = .ok (uint256Value input.v))
    (hr : f.locals["r"]? = some (wordBytes32Value input.r))
    (hs : f.locals["s"]? = some (wordBytes32Value input.s))
    (ho : f.locals["currentOwner"]? = some old)
    (hbody : ExecFuncBody config (ecrecoverFrame input) evm ecrecoverAddressFunction.body
      (.returned f' evm' (some [.address (AccountAddress.ofUInt256 owner)]))) :
    ExecBlock config f evm (signatureRecoverBody digest v)
      (.ok (signatureRecoveredFrame f owner) evm') := by
  have hcall := safeInternalEcrecover hc hd hv hr hs hbody
  exact .consNormal hcall (.consNormal (.assign
    (evalLocalValue (by simp [resumeAfterInternalCall, collapseReturns,
      Std.HashMap.getElem?_insert])) (assignLocalValue (old := old) _ (by
        simp [resumeAfterInternalCall, Std.HashMap.getElem?_insert, ho]))) .nil)

theorem signatureRecoverSourceRejected {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {input : EcrecoverInput} {digest v : Expr} (hc : SignatureCore p f)
    (hd : evalExpr? config f evm digest = .ok (wordBytes32Value input.digest))
    (hv : evalExpr? config f evm v = .ok (uint256Value input.v))
    (hr : f.locals["r"]? = some (wordBytes32Value input.r))
    (hs : f.locals["s"]? = some (wordBytes32Value input.s))
    (hbody : ExecFuncBody config (ecrecoverFrame input) evm
      ecrecoverAddressFunction.body .reverted) :
    ExecBlock config f evm (signatureRecoverBody digest v) .reverted :=
  .consRevert (safeInternalEcrecover hc hd hv hr hs hbody)

theorem SignatureCore.recovered {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (owner : UInt256) :
    SignatureCore p (signatureRecoveredFrame f owner) :=
  (hc.set _ _ (by decide)).current owner

end Benchmarks.Safe
