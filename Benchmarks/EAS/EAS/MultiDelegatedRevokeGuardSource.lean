import Benchmarks.EAS.EAS.MultiDelegatedRevokeSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

theorem multiDelegatedRevokeGuard_eval {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationBatch}
    (hd : L.get? "data" = some (.array (r.data.map RevocationRequestRecord.tuple)))
    (hs : L.get? "signatures" = some (.array (r.signatures.map SignatureRecord.tuple))) :
    evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.unary .not (.binary .or
        (.binary .eq (.arrayLength .localVar {base := "data"}) (.intLit 0))
        (.binary .ne (.arrayLength .localVar {base := "data"}) (.arrayLength .localVar {base := "signatures"})))) =
      .ok (.bool (decide (0<r.data.length ∧ r.data.length=r.signatures.length))) := by
  have hde := evalLocalArrayLength (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hd
  have hse := evalLocalArrayLength (cfg := config) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hs
  simp only [List.length_map] at hde hse
  simp only [evalExpr?,hde,hse,pure,EvalResult.bind,bind,evalBinaryOp?,evalUnaryOp?]
  by_cases h0 : r.data.length = 0
  · simp only [h0,Int.ofNat_zero,beq_self_eq_true,EvalResult.bind,EvalResult.ofOption,
      Bool.not_true,show ¬(0<0 ∧ 0=r.signatures.length) by omega,decide_false]
    rfl
  · have hv0 : (Value.int (Int.ofNat r.data.length) == Value.int 0) = false :=
      beq_eq_false_iff_ne.mpr (by intro h; have he := Value.int.inj h; change (r.data.length : Int) = 0 at he; omega)
    rw [hv0]
    simp only [EvalResult.bind,EvalResult.ofOption,Bool.not_not]
    congr 2
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq,Value.int.injEq,decide_eq_true_eq]
    change ((r.data.length : Int) = (r.signatures.length : Int)) ↔ _
    omega

theorem multiDelegatedRevokeGuardSource {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationBatch}
    (hd : L.get? "data" = some (.array (r.data.map RevocationRequestRecord.tuple)))
    (hs : L.get? "signatures" = some (.array (r.signatures.map SignatureRecord.tuple))) :
    if 0<r.data.length ∧ r.data.length=r.signatures.length then
      ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokeGuard
        (.ok {contract := contract,locals := L,immutables := imms} evm)
    else ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm multiDelegatedRevokeGuard .reverted := by
  have he := multiDelegatedRevokeGuard_eval (imms := imms) (evm := evm) hd hs
  split <;> rename_i h
  · exact ExecStmt.requireTrue (by simpa only [decide_eq_true h] using he)
  · exact ExecStmt.requireFalse (by simpa only [decide_eq_false h] using he)

end Benchmarks.EAS.EAS
