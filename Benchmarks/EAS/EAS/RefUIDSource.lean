import Benchmarks.EAS.EAS.ValidUIDSource
import Benchmarks.EAS.EAS.BoolCallBlock

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def refUIDExpr : Expr := .field (.var "request") "refUID"
def refUIDStmt : Stmt := .ite
  (.binary .ne refUIDExpr (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩)))
  (boolCallBlock "isAttestationValid_body" [refUIDExpr,.var "$EAS.freeMemory"] "__c4$allocation" "__c4") []
def refUIDLocals (L : Store) (uid value : UInt256) (heap : Nat) : Store :=
  if uid = ⟨0⟩ then L else
    unpackHeapLocals (L.insert "__c4$allocation" (.tuple [.bool (decide (value ≠ ⟨0⟩)),.int (Int.ofNat heap)]))
      "__c4" "$EAS.freeMemory" (.bool (decide (value ≠ ⟨0⟩))) heap

theorem refUIDSource {L imms : Store} {evm : EVM.State} {r : AttestationRequestRecord} {heap : Nat}
    (hr : L.get? "request" = some r.struct) (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    if r.refUID = ⟨0⟩ ∨ dbUIDWord evm r.refUID ≠ ⟨0⟩ then
      ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm refUIDStmt
        (.ok {contract := contract,locals := refUIDLocals L r.refUID (dbUIDWord evm r.refUID) heap,immutables := imms} evm)
    else ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm refUIDStmt .reverted := by
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm refUIDExpr = .ok (wordBytes32Value r.refUID) := by
    simp only [refUIDExpr,evalExpr?,hr,EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  have hcond : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.binary .ne refUIDExpr (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩))) =
      .ok (.bool (decide (r.refUID ≠ ⟨0⟩))) := by
    simp only [evalExpr?,he,EvalResult.bind,bind,pure]
    exact evalBytes32Ne _ _
  by_cases hz : r.refUID = ⟨0⟩
  · rw [if_pos (Or.inl hz),refUIDLocals,if_pos hz]
    exact ExecStmt.iteFalse (by simpa only [hz,ne_self_iff_false,decide_false] using hcond) ExecBlock.nil
  · have hc := validUIDCall (fork := fork) (L := L) (imms := imms) (evm := evm) (word := r.refUID) (heap := heap)
      (args := [refUIDExpr,.var "$EAS.freeMemory"]) (retVar := "__c4$allocation") (by
      simp only [evalExprs?,he,evalExpr?,hh,EvalResult.ofOption,EvalResult.bind,bind,pure])
    have hu := unpackHeapResult (fork := fork) (cfg := config) (evm := evm)
      (frame := {contract := contract,locals := L.insert "__c4$allocation" (.tuple [
        .bool (decide (dbUIDWord evm r.refUID ≠ ⟨0⟩)),.int (Int.ofNat heap)]),immutables := imms})
      (tmp := "__c4$allocation") (result := "__c4") (cursor := "$EAS.freeMemory")
      (store_get_self _ _ _)
      (by simpa only [store_get_ne _ _ (by decide : ("__c4$allocation" == "$EAS.freeMemory") = false)] using hh)
      (by decide) (by decide)
    have hb : evalExpr? config {contract := contract,locals := refUIDLocals L r.refUID (dbUIDWord evm r.refUID) heap,immutables := imms}
        evm (.var "__c4") = .ok (.bool (decide (dbUIDWord evm r.refUID ≠ ⟨0⟩))) := by
      simp only [refUIDLocals,if_neg hz,unpackHeapLocals,evalExpr?,
        store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "__c4") = false),store_get_self,EvalResult.ofOption]
    have hcond' : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
        (.binary .ne refUIDExpr (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩))) = .ok (.bool true) := by
      simpa only [decide_eq_true hz] using hcond
    by_cases hv : dbUIDWord evm r.refUID ≠ ⟨0⟩
    · rw [if_pos (Or.inr hv),refUIDLocals,if_neg hz]
      apply ExecStmt.iteTrue hcond'
      apply ExecBlock.consNormal hc
      apply execBlock_append hu
      exact ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [refUIDLocals,if_neg hz,decide_eq_true hv] using hb)) ExecBlock.nil
    · rw [if_neg (by tauto)]
      apply ExecStmt.iteTrue hcond'
      apply ExecBlock.consNormal hc
      apply execBlock_append hu
      exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [refUIDLocals,if_neg hz,decide_eq_false hv] using hb))

end Benchmarks.EAS.EAS
