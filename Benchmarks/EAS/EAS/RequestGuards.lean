import Benchmarks.EAS.EAS.AttestationRequest
import Benchmarks.EAS.EAS.GetSchemaSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def attestTimeExpr : Expr := .unary .not (.binary .and
  (.binary .ne (.field (.var "request") "expirationTime") (.intLit 0))
  (.binary .le (.field (.var "request") "expirationTime") (.var "__c1")))
def attestRevocableExpr : Expr := .unary .not (.binary .and
  (.unary .not (.field (.var "schemaRecord") "revocable")) (.field (.var "request") "revocable"))
def attestRequestGuards : Body := [.require attestTimeExpr,.require attestRevocableExpr]

theorem attestTimeExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State}
    {r : AttestationRequestRecord} {time : UInt256}
    (hr : frame.locals.get? "request" = some r.struct)
    (ht : frame.locals.get? "__c1" = some (.int (Int.ofNat time.toNat))) :
    evalExpr? cfg frame evm attestTimeExpr = .ok (.bool (decide (r.expirationTime.toNat = 0 ∨ time.toNat < r.expirationTime.toNat))) := by
  have he : evalExpr? cfg frame evm (.field (.var "request") "expirationTime") = .ok (.int (Int.ofNat r.expirationTime.toNat)) := by
    simp only [evalExpr?,hr,EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  have hne : evalExpr? cfg frame evm (.binary .ne (.field (.var "request") "expirationTime") (.intLit 0)) =
      .ok (.bool (decide (r.expirationTime.toNat ≠ 0))) := by
    have hval : (Value.int (Int.ofNat r.expirationTime.toNat) == Value.int 0) = decide (r.expirationTime.toNat = 0) := by
      apply Bool.eq_iff_iff.mpr
      simp only [beq_iff_eq,Value.int.injEq,Int.ofNat_eq_natCast,Int.natCast_eq_zero,decide_eq_true_eq]
    simp only [evalExpr?,he,EvalResult.bind,bind,pure,evalBinaryOp?,hval,decide_not]
  have hle := naturalLeSource he (show evalExpr? cfg frame evm (.var "__c1") = .ok (.int (Int.ofNat time.toNat)) by
    simp only [evalExpr?,ht,EvalResult.ofOption])
  by_cases hz : r.expirationTime.toNat = 0
  · simp only [attestTimeExpr,evalExpr?,hne,hz,ne_self_iff_false,decide_false,EvalResult.bind,bind,pure,
      evalUnaryOp?,EvalResult.ofOption,Bool.not_false,true_or,decide_true]
  · simp only [attestTimeExpr,evalExpr?,hne,decide_eq_true hz,hle,EvalResult.bind,bind,pure,evalUnaryOp?,EvalResult.ofOption]
    simp only [hz,false_or,← decide_not,not_le]

theorem attestRevocableExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State}
    {r : AttestationRequestRecord} {s : SchemaRecord}
    (hr : frame.locals.get? "request" = some r.struct) (hs : frame.locals.get? "schemaRecord" = some s.value) :
    evalExpr? cfg frame evm attestRevocableExpr = .ok (.bool (s.revocable || !r.revocable)) := by
  have he : evalExpr? cfg frame evm (.field (.var "request") "revocable") = .ok (.bool r.revocable) := by
    simp only [evalExpr?,hr,EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  have hf : evalExpr? cfg frame evm (.field (.var "schemaRecord") "revocable") = .ok (.bool s.revocable) := by
    simp only [evalExpr?,hs,EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  simp only [attestRevocableExpr,evalExpr?,he,hf,EvalResult.bind,bind,pure,evalBinaryOp?,evalUnaryOp?]
  cases s.revocable <;> cases r.revocable <;> rfl

theorem attestRequestGuards_source {L imms : Store} {evm : EVM.State}
    {r : AttestationRequestRecord} {s : SchemaRecord} {time : UInt256}
    (hr : L.get? "request" = some r.struct) (hs : L.get? "schemaRecord" = some s.value)
    (ht : L.get? "__c1" = some (.int (Int.ofNat time.toNat))) :
    if (r.expirationTime.toNat = 0 ∨ time.toNat < r.expirationTime.toNat) ∧ (s.revocable || !r.revocable) = true then
      ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestRequestGuards
        (.ok {contract := contract,locals := L,immutables := imms} evm)
    else ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestRequestGuards .reverted := by
  have he := attestTimeExpr_eval (cfg := config) (frame := {contract := contract,locals := L,immutables := imms}) (evm := evm) hr ht
  have hf := attestRevocableExpr_eval (cfg := config) (frame := {contract := contract,locals := L,immutables := imms}) (evm := evm) hr hs
  by_cases htime : r.expirationTime.toNat = 0 ∨ time.toNat < r.expirationTime.toNat
  · have ht := ExecStmt.requireTrue (fork := fork) (by simpa only [decide_eq_true htime] using he)
    cases hb : s.revocable || !r.revocable with
    | false =>
      rw [if_neg (by simp only [hb,Bool.false_eq_true,and_false,not_false_eq_true])]
      exact ExecBlock.consNormal ht (ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [hb] using hf)))
    | true =>
      rw [if_pos ⟨htime,rfl⟩]
      exact ExecBlock.consNormal ht (ExecBlock.consNormal (ExecStmt.requireTrue (by simpa only [hb] using hf)) ExecBlock.nil)
  · rw [if_neg (by tauto)]
    exact ExecBlock.consRevert (ExecStmt.requireFalse (by simpa only [decide_eq_false htime] using he))

end Benchmarks.EAS.EAS
