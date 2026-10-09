import Benchmarks.Safe.SafeMulSource
import Benchmarks.Safe.SignatureValues

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

structure SignatureInput where
  executor : EVM.Address
  hash : UInt256
  signatures : ByteArray
  required : UInt256

namespace SignatureInput

def requiredBytes (p : SignatureInput) : Nat := p.required.toNat * 65

def args (p : SignatureInput) : Store :=
  ((((∅ : Store).insert "requiredSignatures" (uint256Value p.required)).insert
    "signatures" (.bytes p.signatures)).insert "dataHash" (wordBytes32Value p.hash)).insert
    "executor" (.address p.executor)

def frame (p : SignatureInput) : Frame := { contract := contract, locals := p.args }

def requiredFrame (p : SignatureInput) : Frame :=
  { p.frame with locals := p.args.insert "requiredBytes" (.int (Int.ofNat p.requiredBytes)) }

def loopFrame (p : SignatureInput) : Frame :=
  { p.requiredFrame with locals := ((p.requiredFrame.locals.insert "lastOwner"
    (.address (AccountAddress.ofNat 0))).insert "currentOwner"
      (.address (AccountAddress.ofNat 0))).insert "i" (.int 0) }

end SignatureInput

def signatureLoopCondition : Expr := ltE (.var "i") (.var "requiredSignatures")

def signatureLoopBody : List Stmt :=
  match checkNSignaturesImplFunction.body[5]! with
  | .while _ body => body
  | _ => []

theorem safeSignatureRequiredBytes (p : SignatureInput) (evm : EVM.State)
    (hfit : p.requiredBytes < UInt256.size) :
    ExecStmt config p.frame evm
      (.internalCall "_mul" [.var "requiredSignatures", .intLit 65] "requiredBytes")
      (.ok p.requiredFrame evm) := by
  have hm : (UInt256.mul p.required ⟨65⟩).toNat = p.requiredBytes := by
    rw [u256_mul_toNat]
    exact Nat.mod_eq_of_lt hfit
  have h := safeInternalMul (caller := p.frame) (evm := evm) (a := p.required) (b := ⟨65⟩)
    (lhs := .var "requiredSignatures") (rhs := .intLit 65) (retVar := "requiredBytes") rfl
    (evalLocalValue (by simp [SignatureInput.frame, SignatureInput.args,
      Std.HashMap.getElem_insert])) (by simp [evalExpr?, uint256Value]; rfl) hfit
  simpa only [uint256Value, hm] using h

theorem evalSignatureLengthBound (p : SignatureInput) (evm : EVM.State) :
    evalExpr? config p.requiredFrame evm
      (geE (localLength "signatures") (.var "requiredBytes")) =
      .ok (.bool (decide (p.requiredBytes ≤ p.signatures.size))) := by
  have hl := evalLocalBytesLength (cfg := config) (evm := evm) (frame := p.requiredFrame)
    (name := "signatures") (bytes := p.signatures) (by
      simp [SignatureInput.requiredFrame, SignatureInput.frame, SignatureInput.args,
        Std.HashMap.getElem_insert])
  have hr : evalExpr? config p.requiredFrame evm (.var "requiredBytes") =
      .ok (.int (Int.ofNat p.requiredBytes)) := evalLocalValue (by
    simp [SignatureInput.requiredFrame, Std.HashMap.getElem_insert])
  change evalExpr? config p.requiredFrame evm (localLength "signatures") = _ at hl
  rw [geE, evalExpr?, hl, hr] <;>
    simp [EvalResult.bind, bind, evalBinaryOp?, Int.ofNat_eq_natCast, pure]

theorem safeSignatureBoundsFailed (p : SignatureInput) (evm : EVM.State)
    (hbad : p.signatures.size < p.requiredBytes) :
    ExecFuncBody config p.frame evm checkNSignaturesImplFunction.body .reverted := by
  by_cases hfit : p.requiredBytes < UInt256.size
  · apply ExecFuncBody.execBlockRevert
    exact .consNormal (safeSignatureRequiredBytes p evm hfit) (.consRevert
      (.requireFalse (by simpa only [decide_false, not_le.mpr hbad]
        using evalSignatureLengthBound p evm)))
  · apply ExecFuncBody.execBlockRevert
    apply ExecBlock.consRevert
    apply safeInternalMulOverflow (a := p.required) (b := ⟨65⟩) rfl
    · exact evalLocalValue (by simp [SignatureInput.frame, SignatureInput.args,
        Std.HashMap.getElem_insert])
    · simp [evalExpr?, uint256Value]
      rfl
    · exact Nat.le_of_not_gt hfit

theorem safeSignatureSourcePrefix (p : SignatureInput) (evm : EVM.State)
    {result : ExecResult} (hn : p.signatures.size < UInt256.size)
    (hbound : p.requiredBytes ≤ p.signatures.size)
    (htail : ExecBlock config p.loopFrame evm
      [.while signatureLoopCondition signatureLoopBody] result) :
    ExecFuncBody config p.frame evm checkNSignaturesImplFunction.body
      (match result with
      | .ok f e => .returned f e none
      | .break f e => .returned f e none
      | .continue f e => .returned f e none
      | .returned f e value => .returned f e value
      | .reverted => .reverted
      | .staticViolation => .staticViolation) := by
  have hz {f : Frame} : evalExpr? config f evm zeroAddr =
      .ok (.address (AccountAddress.ofNat 0)) := by
    simp [zeroAddr, evalExpr?, castValue?, addrSt, EvalResult.ofOption,
      EvalResult.bind, bind, pure, intToNat?]
  have hr : ExecBlock config p.frame evm checkNSignaturesImplFunction.body result := by
    apply ExecBlock.consNormal (safeSignatureRequiredBytes p evm (by omega))
    apply ExecBlock.consNormal (.requireTrue (by
      simpa only [hbound, decide_true] using evalSignatureLengthBound p evm))
    exact .consNormal (.letDecl hz) (.consNormal (.letDecl hz)
      (.consNormal (.letDecl (by simp [evalExpr?, pure])) htail))
  cases result with
  | ok => exact .execBlockOK hr
  | «break» => exact .execBlockBreak hr
  | «continue» => exact .execBlockContinue hr
  | returned => exact .execBlockRet hr
  | reverted => exact .execBlockRevert hr
  | staticViolation => exact .execBlockStatic hr

end Benchmarks.Safe
