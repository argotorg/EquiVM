import Benchmarks.Safe.SafeAddSource
import Benchmarks.Safe.SignatureValues
import Benchmarks.Safe.ContractSignatureSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxHeartbeats 1000000

structure ContractSignatureInput where
  owner : EVM.Address
  hash : UInt256
  signatures : ByteArray
  offset : UInt256

namespace ContractSignatureInput

def start (p : ContractSignatureInput) : Nat := p.offset.toNat + 32

def len (p : ContractSignatureInput) : UInt256 := calldataWord p.signatures p.offset.toNat

def finish (p : ContractSignatureInput) : Nat := p.start + p.len.toNat

def signature (p : ContractSignatureInput) : ByteArray := p.signatures.extract p.start p.finish

def args (p : ContractSignatureInput) : Store :=
  ((((∅ : Store).insert "offset" (uint256Value p.offset)).insert
    "signatures" (.bytes p.signatures)).insert "dataHash" (wordBytes32Value p.hash)).insert
      "owner" (.address p.owner)

def frame (p : ContractSignatureInput) : Frame := { contract := contract, locals := p.args }

def startFrame (p : ContractSignatureInput) : Frame :=
  { p.frame with locals := p.args.insert "signatureDataStart" (.int (Int.ofNat p.start)) }

def lengthFrame (p : ContractSignatureInput) : Frame :=
  { p.startFrame with
    locals := p.startFrame.locals.insert "contractSignatureLen" (uint256Value p.len) }

def endFrame (p : ContractSignatureInput) : Frame :=
  { p.lengthFrame with
    locals := p.lengthFrame.locals.insert "signatureDataEnd" (.int (Int.ofNat p.finish)) }

def sliceFrame (p : ContractSignatureInput) : Frame :=
  { p.endFrame with locals := p.endFrame.locals.insert "contractSignature" (.bytes p.signature) }

def finalFrame (p : ContractSignatureInput) (valid : Bool) : Frame :=
  { p.sliceFrame with locals := p.sliceFrame.locals.insert "valid" (.bool valid) }

end ContractSignatureInput

open ContractSignatureInput

theorem safeCheckContractStart (p : ContractSignatureInput) (evm : EVM.State)
    (hf : p.start < UInt256.size) :
    ExecStmt config p.frame evm
      (.internalCall "_add" [.var "offset", .intLit 32] "signatureDataStart")
      (.ok p.startFrame evm) := by
  have he : (p.offset + (⟨32⟩ : UInt256)).toNat = p.start :=
    addWord_toNat _ _ hf
  have h := safeInternalAdd (caller := p.frame) (evm := evm) (a := p.offset) (b := ⟨32⟩) rfl
    (lhs := .var "offset") (rhs := .intLit 32) (retVar := "signatureDataStart")
    (by simp [evalExpr?, frame, args, EvalResult.ofOption, Std.HashMap.getElem_insert])
    (by simp [evalExpr?]; rfl) hf
  simpa only [uint256Value, he] using h

theorem safeCheckContractStartBound (p : ContractSignatureInput) (evm : EVM.State) :
    evalExpr? config p.startFrame evm
      (leE (.var "signatureDataStart") (localLength "signatures")) =
      .ok (.bool (decide (p.start ≤ p.signatures.size))) := by
  apply naturalLeSource
  · exact evalLocalValue (by simp [startFrame, Std.HashMap.getElem_insert])
  · exact evalLocalBytesLength (by
      simp [startFrame, frame, args, Std.HashMap.getElem_insert])

theorem safeCheckContractLength (p : ContractSignatureInput) (evm : EVM.State)
    (hb : p.start ≤ p.signatures.size) :
    evalExpr? config p.startFrame evm
      (signatureUintAt (.var "signatures") (.var "offset")) = .ok (uint256Value p.len) := by
  apply evalSignatureUintAt
  · exact evalLocalValue (by simp [startFrame, frame, args, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [startFrame, frame, args, Std.HashMap.getElem_insert])
  · exact hb

theorem safeCheckContractEnd (p : ContractSignatureInput) (evm : EVM.State)
    (hf : p.finish < UInt256.size) :
    ExecStmt config p.lengthFrame evm
      (.internalCall "_add" [.var "signatureDataStart", .var "contractSignatureLen"]
        "signatureDataEnd") (.ok p.endFrame evm) := by
  have hs : p.start < UInt256.size := by dsimp [finish] at hf; omega
  have ha : (UInt256.ofNat p.start).toNat = p.start := ulit_toNat' _ hs
  have he : (UInt256.ofNat p.start + p.len).toNat = p.finish := by
    have hh := addWord_toNat (UInt256.ofNat p.start) p.len (by rw [ha]; exact hf)
    simpa only [ha] using hh
  have h := safeInternalAdd (caller := p.lengthFrame) (evm := evm) (a := UInt256.ofNat p.start)
    (b := p.len) rfl (lhs := .var "signatureDataStart") (rhs := .var "contractSignatureLen")
    (retVar := "signatureDataEnd")
    (by simp only [uint256Value, ha]
        exact evalLocalValue (by simp [lengthFrame, startFrame, Std.HashMap.getElem_insert]))
    (evalLocalValue (by simp [lengthFrame, Std.HashMap.getElem_insert]))
    (by rw [ha]; exact hf)
  simpa only [uint256Value, he] using h

theorem safeCheckContractEndBound (p : ContractSignatureInput) (evm : EVM.State) :
    evalExpr? config p.endFrame evm
      (leE (.var "signatureDataEnd") (localLength "signatures")) =
      .ok (.bool (decide (p.finish ≤ p.signatures.size))) := by
  apply naturalLeSource
  · exact evalLocalValue (by simp [endFrame, Std.HashMap.getElem_insert])
  · exact evalLocalBytesLength (by
      simp [endFrame, lengthFrame, startFrame, frame, args, Std.HashMap.getElem_insert])

theorem safeCheckContractSlice (p : ContractSignatureInput) (evm : EVM.State)
    (hb : p.finish ≤ p.signatures.size) :
    evalExpr? config p.endFrame evm
      (.bytesSlice (.var "signatures") (.var "signatureDataStart") (.var "signatureDataEnd")) =
      .ok (.bytes p.signature) := by
  apply evalBytesSlice
  · exact evalLocalValue (by
      simp [endFrame, lengthFrame, startFrame, frame, args, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by
      simp [endFrame, lengthFrame, startFrame, Std.HashMap.getElem_insert])
  · exact evalLocalValue (by simp [endFrame, Std.HashMap.getElem_insert])
  · dsimp [finish]; omega
  · exact hb

theorem safeCheckContractCall (p : ContractSignatureInput) {evm evm' : EVM.State}
    {z : Bool} {out : ByteArray}
    (hc : callViaEVM evm (EVM.address p.owner) 0 (contractSignatureCallBytes p.hash p.signature)
      (z, evm', out) false) :
    ExecStmt config p.sliceFrame evm
      (.internalCall "validateContractSignature"
        [.var "owner", .var "dataHash", .var "contractSignature"] "valid")
      (.ok (p.finalFrame (contractSignatureResult z out)) evm') := by
  apply internalCallFunctionReturn (callee := validateContractSignatureFunction)
    (argVals := [.address p.owner, wordBytes32Value p.hash, .bytes p.signature])
    (locals := contractSignatureArgs p.owner p.hash p.signature)
    (calleeSolm := contractSignatureFinalFrame p.owner p.hash p.signature z out)
    (value := some [.bool (contractSignatureResult z out)])
  · simp [sliceFrame, endFrame, lengthFrame, startFrame, frame, args,
      evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
      Std.HashMap.getElem_insert]
  · rfl
  · rfl
  · exact safeContractSignatureSource hc

theorem safeCheckContractSourcePrefix (p : ContractSignatureInput) (evm : EVM.State)
    (hs : p.start ≤ p.signatures.size) (he : p.finish ≤ p.signatures.size)
    (hb : p.signatures.size < UInt256.size) {result : ExecResult}
    (ht : ExecBlock config p.sliceFrame evm
      [.internalCall "validateContractSignature"
        [.var "owner", .var "dataHash", .var "contractSignature"] "valid",
        .require (.var "valid")] result) :
    ExecBlock config p.frame evm checkContractSignatureFunction.body result := by
  refine .consNormal (safeCheckContractStart p evm (by omega))
    (.consNormal (.requireTrue ?_) (.consNormal (.letDecl (safeCheckContractLength p evm hs))
      (.consNormal (safeCheckContractEnd p evm (by omega))
        (.consNormal (.requireTrue ?_) (.consNormal (.letDecl (safeCheckContractSlice p evm he))
          ht)))))
  · simpa only [hs, decide_true] using safeCheckContractStartBound p evm
  · simpa only [he, decide_true] using safeCheckContractEndBound p evm

theorem safeCheckContractSource (p : ContractSignatureInput) {evm evm' : EVM.State}
    {z : Bool} {out : ByteArray} (hs : p.start ≤ p.signatures.size)
    (he : p.finish ≤ p.signatures.size) (hb : p.signatures.size < UInt256.size)
    (hc : callViaEVM evm (EVM.address p.owner) 0 (contractSignatureCallBytes p.hash p.signature)
      (z, evm', out) false) :
    ExecFuncBody config p.frame evm checkContractSignatureFunction.body
      (if contractSignatureResult z out then
        .returned (p.finalFrame true) evm' none else .reverted) := by
  have hv : evalExpr? config (p.finalFrame (contractSignatureResult z out)) evm'
      (.var "valid") = .ok (.bool (contractSignatureResult z out)) :=
    evalLocalValue (by simp [finalFrame, Std.HashMap.getElem_insert])
  cases hz : contractSignatureResult z out
  · simp only [hz, Bool.false_eq_true, if_false]
    apply ExecFuncBody.execBlockRevert
    apply safeCheckContractSourcePrefix p evm hs he hb
    exact .consNormal (safeCheckContractCall p hc)
      (.consRevert (.requireFalse (by simpa only [hz] using hv)))
  · simp only [hz, if_true]
    apply ExecFuncBody.execBlockOK
    apply safeCheckContractSourcePrefix p evm hs he hb
    have ht := ExecBlock.consNormal (safeCheckContractCall p hc)
      (ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [hz] using hv)) ExecBlock.nil)
    simpa only [hz] using ht

theorem safeCheckContractBoundsFailed (p : ContractSignatureInput) (evm : EVM.State)
    (hbad : ¬(p.start ≤ p.signatures.size ∧ p.finish ≤ p.signatures.size)) :
    ExecFuncBody config p.frame evm checkContractSignatureFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  by_cases hsfit : p.start < UInt256.size
  swap
  · apply ExecBlock.consRevert
    apply safeInternalAddOverflow (a := p.offset) (b := ⟨32⟩) rfl
    · exact evalLocalValue (by simp [frame, args, Std.HashMap.getElem_insert])
    · simp [evalExpr?]; rfl
    · exact Nat.le_of_not_gt hsfit
  refine .consNormal (safeCheckContractStart p evm hsfit) ?_
  by_cases hs : p.start ≤ p.signatures.size
  swap
  · exact .consRevert (.requireFalse (by
      simpa only [hs, decide_false] using safeCheckContractStartBound p evm))
  refine .consNormal (.requireTrue (by
    simpa only [hs, decide_true] using safeCheckContractStartBound p evm))
    (.consNormal (.letDecl (safeCheckContractLength p evm hs)) ?_)
  by_cases hefit : p.finish < UInt256.size
  swap
  · apply ExecBlock.consRevert
    have ha : (UInt256.ofNat p.start).toNat = p.start := ulit_toNat' _ hsfit
    apply safeInternalAddOverflow (a := UInt256.ofNat p.start) (b := p.len) rfl
    · simp only [uint256Value, ha]
      exact evalLocalValue (by simp [lengthFrame, startFrame, Std.HashMap.getElem_insert])
    · exact evalLocalValue (by simp [lengthFrame, Std.HashMap.getElem_insert])
    · rw [ha]
      exact Nat.le_of_not_gt hefit
  refine .consNormal (safeCheckContractEnd p evm hefit) (.consRevert (.requireFalse ?_))
  have he : ¬p.finish ≤ p.signatures.size := fun he ↦ hbad ⟨hs, he⟩
  simpa only [he, decide_false] using safeCheckContractEndBound p evm

end Benchmarks.Safe
