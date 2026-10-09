import Benchmarks.Safe.CheckNSignaturesSource
import Benchmarks.Safe.SignatureBranchSource
import Benchmarks.Safe.OwnerCount

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

structure SignatureCheckInput where
  executor : EVM.Address
  hash : UInt256
  signatures : ByteArray

namespace SignatureCheckInput

def args (p : SignatureCheckInput) : Store :=
  (((∅ : Store).insert "signatures" (.bytes p.signatures)).insert "dataHash"
    (wordBytes32Value p.hash)).insert "executor" (.address p.executor)

def frame (p : SignatureCheckInput) : Frame := { contract := contract, locals := p.args }

def thresholdFrame (p : SignatureCheckInput) (threshold : UInt256) : Frame :=
  signatureSet p.frame "_threshold" (uint256Value threshold)

def withRequired (p : SignatureCheckInput) (threshold : UInt256) : SignatureInput :=
  ⟨p.executor, p.hash, p.signatures, threshold⟩

end SignatureCheckInput

theorem evalSignatureCheckThreshold (p : SignatureCheckInput) (evm : EVM.State) :
    evalExpr? config p.frame evm (.storage thresholdRef) =
      .ok (uint256Value (storedThreshold evm)) :=
  safeEvalStoredThreshold evm p.args (by
    simp [SignatureCheckInput.args, Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert])

theorem evalSignatureCheckNonzero (p : SignatureCheckInput) (evm : EVM.State)
    (threshold : UInt256) :
    evalExpr? config (p.thresholdFrame threshold) evm (neE (.var "_threshold") (.intLit 0)) =
      .ok (.bool (decide (threshold.toNat ≠ 0))) := by
  have ht : evalExpr? config (p.thresholdFrame threshold) evm (.var "_threshold") =
      .ok (uint256Value threshold) := evalLocalValue (by
    simp [SignatureCheckInput.thresholdFrame, signatureSet, Std.HashMap.getElem?_insert])
  rw [neE, evalExpr_binary_nonshort (by decide) (by decide), ht]
  simp [evalExpr?, evalBinaryOp?, EvalResult.bind, bind, pure, uint256Value]
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, Value.int.injEq, decide_eq_true_eq, Int.natCast_eq_zero]

theorem signatureCheckZero (p : SignatureCheckInput) (evm : EVM.State)
    (hz : storedThreshold evm = ⟨0⟩) :
    ExecFuncBody config p.frame evm checkSignaturesImplFunction.body .reverted := by
  apply ExecFuncBody.execBlockRevert
  exact .consNormal (.letDecl (evalSignatureCheckThreshold p evm))
    (.consRevert (.requireFalse (by
      simpa only [hz, show (⟨0⟩ : UInt256).toNat = 0 from rfl, ne_eq, not_true_eq_false,
        decide_false] using evalSignatureCheckNonzero p evm (storedThreshold evm))))

theorem signatureCheckSource (p : SignatureCheckInput) (evm : EVM.State) {result : ExecResult}
    (hn : storedThreshold evm ≠ ⟨0⟩)
    (hbody : ExecFuncBody config (p.withRequired (storedThreshold evm)).frame evm
      checkNSignaturesImplFunction.body result) :
    ExecBlock config p.frame evm checkSignaturesImplFunction.body
      (internalCallResult (p.thresholdFrame (storedThreshold evm)) "_checked" result) := by
  have ht : (storedThreshold evm).toNat ≠ 0 := fun hh ↦ hn (u256_inj hh)
  have hcall : ExecStmt config (p.thresholdFrame (storedThreshold evm)) evm
      (.internalCall "checkNSignaturesImpl"
        [.var "executor", .var "dataHash", .var "signatures", .var "_threshold"] "_checked")
      (internalCallResult (p.thresholdFrame (storedThreshold evm)) "_checked" result) := by
    apply safeInternalCheckNSignatures (p := p.withRequired (storedThreshold evm)) rfl rfl
      (hbody := hbody) <;> apply evalLocalValue <;>
      simp [SignatureCheckInput.thresholdFrame, SignatureCheckInput.frame,
        SignatureCheckInput.args, SignatureCheckInput.withRequired, signatureSet,
        Std.HashMap.getElem?_insert, Std.HashMap.getElem_insert]
  exact .consNormal (.letDecl (evalSignatureCheckThreshold p evm))
    (.consNormal (.requireTrue (by
      exact (evalSignatureCheckNonzero p evm (storedThreshold evm)).trans
        (by congr 2; exact decide_eq_true ht)))
      (execBlock_singleton hcall))

end Benchmarks.Safe
