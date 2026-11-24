import Benchmarks.Safe.V2_0e91d99.SignatureP256Decode
import Benchmarks.Safe.V2_0e91d99.InternalCall

variable {fork : Ethereum.Fork}

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe.V2_0e91d99

set_option maxRecDepth 100000

def signatureP256Frame (p : SignatureInput) (f : Frame) (r s : UInt256) : Frame :=
  signatureP256SignerFrame (signatureP256EndFrame f r s) (signatureP256Input p s)

def signatureP256FinalFrame (p : SignatureInput) (f : Frame) (r s : UInt256) : Frame :=
  signatureSet (signatureP256Frame p f r s) "p256Valid" (.bool true)

theorem SignatureCore.p256Decoded {p : SignatureInput} {f : Frame}
    (hc : SignatureCore p f) (r s : UInt256) :
    SignatureCore p (signatureP256Frame p f r s) :=
  (((((hc.p256End r s).set _ _ (by decide)).set _ _ (by decide)).set _ _
    (by decide)).set _ _ (by decide)).set _ _ (by decide)

theorem signatureP256DecodedSource {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {old : Value} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hl : p.requiredBytes ≤ s.toNat) (hh : s.toNat + 128 ≤ p.signatures.size)
    (hb : p.signatures.size < UInt256.size) :
    ExecBlock fork config f evm (signatureP256Body.take 10)
      (.ok (signatureP256Frame p f r s) evm) := by
  have h₁ := signatureP256Prefix (fork := fork) (evm := evm) hc hr hs ho hl hh hb
  have h₂ := signatureP256DecodeSource (fork := fork) (evm := evm) (s := s) (hc.p256End r s)
    (oldR := wordBytes32Value r) (oldS := wordBytes32Value s)
    (by simp [signatureP256EndFrame, signatureP256OffsetFrame, signatureDynamicFrame,
      signatureCurrentFrame, signatureSet, Std.HashMap.getElem?_insert, hr])
    (by simp [signatureP256EndFrame, signatureP256OffsetFrame, signatureDynamicFrame,
      signatureCurrentFrame, signatureSet, Std.HashMap.getElem?_insert, hs])
    (by simp [signatureP256EndFrame, signatureP256OffsetFrame, signatureDynamicFrame,
      signatureSet, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]) hh
  exact execBlock_append_ok h₁ h₂

theorem signatureP256SignerGuard {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} :
    evalExpr? config (signatureP256Frame p f r s) evm
      (eqE (.var "currentOwner") (.var "signerAddress")) =
      .ok (.bool (decide (UInt256.land solcAddrMask r =
        UInt256.land solcAddrMask (p256SignerWord (signatureP256Input p s))))) := by
  apply evalP256SignerMatches
  · simp [signatureP256Frame, signatureP256SignerFrame, signatureP256ReadFrame,
      signatureP256EndFrame, signatureP256OffsetFrame, signatureDynamicFrame,
      signatureCurrentFrame, signatureSet, Std.HashMap.getElem?_insert,
      Std.HashMap.getElem_insert]
  · simp [signatureP256Frame, signatureP256SignerFrame, signatureSet,
      Std.HashMap.getElem?_insert]

theorem safeInternalP256 {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {input : P256Input} {result : ExecResult} (hc : SignatureCore p f)
    (hh : f.locals["dataHash"]? = some (wordBytes32Value input.hash))
    (hr : f.locals["r"]? = some (wordBytes32Value input.r))
    (hs : f.locals["s"]? = some (wordBytes32Value input.s))
    (hx : f.locals["qx"]? = some (uint256Value input.qx))
    (hy : f.locals["qy"]? = some (uint256Value input.qy))
    (hbody : ExecFuncBody fork config input.frame evm p256VerifyFunction.body result) :
    ExecStmt fork config f evm signatureP256Body[11]!
      (internalCallResult f "p256Valid" result) := by
  apply internalCallFunctionResult (callee := p256VerifyFunction)
    (argVals := [wordBytes32Value input.hash, wordBytes32Value input.r,
      wordBytes32Value input.s, uint256Value input.qx, uint256Value input.qy])
    (locals := input.args)
  · simp [evalExprs?, evalLocalValue hh, evalLocalValue hr, evalLocalValue hs,
      evalLocalValue hx, evalLocalValue hy, EvalResult.bind, bind, pure]
  · rw [hc.contract]; rfl
  · rfl
  · convert hbody using 1
    simp only [P256Input.frame, hc.contract, hc.immutables]

theorem signatureP256SignerRejected {p : SignatureInput} {f : Frame} {evm : EVM.State}
    {r s : UInt256} {old : Value} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hl : p.requiredBytes ≤ s.toNat) (hh : s.toNat + 128 ≤ p.signatures.size)
    (hb : p.signatures.size < UInt256.size)
    (hm : UInt256.land solcAddrMask r ≠
      UInt256.land solcAddrMask (p256SignerWord (signatureP256Input p s))) :
    ExecBlock fork config f evm signatureP256Body .reverted := by
  have ht : ExecBlock fork config (signatureP256Frame p f r s) evm
      (signatureP256Body.drop 10) .reverted := .consRevert (.requireFalse (by
        simpa only [hm, decide_false] using
          signatureP256SignerGuard (p := p) (f := f) (r := r) (s := s) (evm := evm)))
  simpa only [List.take_append_drop] using
    execBlock_append_ok (signatureP256DecodedSource hc hr hs ho hl hh hb) ht

theorem signatureP256Source {p : SignatureInput} {f : Frame} {evm evm' : EVM.State}
    {r s : UInt256} {old : Value} {b : Bool} {f' : Frame} (hc : SignatureCore p f)
    (hr : f.locals["r"]? = some (wordBytes32Value r))
    (hs : f.locals["s"]? = some (wordBytes32Value s))
    (ho : f.locals["currentOwner"]? = some old)
    (hl : p.requiredBytes ≤ s.toNat) (hh : s.toNat + 128 ≤ p.signatures.size)
    (hb : p.signatures.size < UInt256.size)
    (hm : UInt256.land solcAddrMask r =
      UInt256.land solcAddrMask (p256SignerWord (signatureP256Input p s)))
    (hbody : ExecFuncBody fork config (signatureP256Input p s).frame evm p256VerifyFunction.body
      (.returned f' evm' (some [.bool b]))) :
    ExecBlock fork config f evm signatureP256Body
      (if b then .ok (signatureP256FinalFrame p f r s) evm' else .reverted) := by
  have hcall := safeInternalP256 (input := signatureP256Input p s) (hc.p256Decoded r s)
    (hc.p256Decoded r s).hash
    (by simp [signatureP256Frame, signatureP256SignerFrame, signatureP256ReadFrame,
      signatureSet, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [signatureP256Frame, signatureP256SignerFrame, signatureP256ReadFrame,
      signatureSet, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [signatureP256Frame, signatureP256SignerFrame, signatureP256ReadFrame,
      signatureSet, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])
    (by simp [signatureP256Frame, signatureP256SignerFrame, signatureP256ReadFrame,
      signatureSet, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]) hbody
  have ht : ExecBlock fork config (signatureP256Frame p f r s) evm (signatureP256Body.drop 10)
      (if b then .ok (signatureP256FinalFrame p f r s) evm' else .reverted) := by
    apply ExecBlock.consNormal (.requireTrue (by
      simpa only [hm, decide_true] using
        signatureP256SignerGuard (p := p) (f := f) (r := r) (s := s) (evm := evm)))
    apply ExecBlock.consNormal hcall
    cases b
    · exact .consRevert (.requireFalse (evalLocalValue (by
        simp [resumeAfterInternalCall, collapseReturns, Std.HashMap.getElem?_insert])))
    · exact .consNormal (.requireTrue (evalLocalValue (by
        simp [resumeAfterInternalCall, collapseReturns, Std.HashMap.getElem?_insert]))) .nil
  simpa only [List.take_append_drop] using
    execBlock_append_ok (signatureP256DecodedSource hc hr hs ho hl hh hb) ht

end Benchmarks.Safe.V2_0e91d99
