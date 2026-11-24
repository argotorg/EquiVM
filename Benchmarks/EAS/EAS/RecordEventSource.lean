import Benchmarks.EAS.EAS.RecordArraysSource
import Benchmarks.EAS.EAS.Allocate

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def recordEventBody : Body := [
  .emit "Attested" [.field (.var "request") "recipient",.var "attester",.var "uid",.var "schema"],
  .assign .localVar {base := "i"} (.cast (.binary .add (.var "i") (.intLit 1)) (.elem (.int abiUInt256Int)))]

theorem recordEventSource {L imms : Store} {evm : EVM.State} {r : AttestationRequestRecord}
    {attester : AccountAddress} {uid schema : UInt256} {i : Nat}
    (hr : L.get? "request" = some r.struct) (ha : L.get? "attester" = some (.address attester))
    (hu : L.get? "uid" = some (wordBytes32Value uid)) (hs : L.get? "schema" = some (wordBytes32Value schema))
    (hi : L.get? "i" = some (.int (Int.ofNat i))) (hb : i+1 < UInt256.size)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm recordEventBody
      (.ok {contract := contract,locals := L.insert "i" (.int (Int.ofNat (i+1))),immutables := imms} evm) := by
  have hrecipient : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.field (.var "request") "recipient") = .ok (.address r.recipient) := by
    simp only [evalExpr?,hr,EvalResult.ofOption,EvalResult.bind,bind]
    rfl
  refine ExecBlock.consNormal (ExecStmt.emit (fork := fork) (hperm := hperm) (vals := [
    .address r.recipient,.address attester,wordBytes32Value uid,wordBytes32Value schema]) ?_) ?_
  · simp only [evalExprs?,hrecipient,evalExpr?,ha,hu,hs,EvalResult.ofOption,EvalResult.bind,bind,pure]
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := Or.inl rfl) (value := .int (Int.ofNat (i+1))) ?_ (assignLocalBase_ok hi)) ExecBlock.nil
  have he := evalCastUint256Add (cfg := config) (evm := evm)
    (frame := {contract := contract,locals := L,immutables := imms})
    (x := i) (y := 1) (a := .var "i") (b := .intLit 1)
    (by simp only [evalExpr?,hi,EvalResult.ofOption]) (by simp only [evalExpr?]; rfl)
  rw [Nat.mod_eq_of_lt hb] at he
  exact he

end Benchmarks.EAS.EAS
