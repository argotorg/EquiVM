import Benchmarks.EAS.EAS.AttestationRequest
import Benchmarks.EAS.EAS.UIDLoopSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def newAttestation (r : AttestationRequestRecord) (schema time : UInt256) (attester : AccountAddress) : AttestationRecord :=
  ⟨⟨0⟩,schema,time,r.expirationTime,⟨0⟩,r.refUID,r.recipient,attester,r.revocable,r.data⟩
def newAttestationExpr : Expr := .structLit "Attestation" [
  ("uid",.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩)),("schema",.var "schema"),("time",.var "__c2"),
  ("expirationTime",.field (.var "request") "expirationTime"),("revocationTime",.intLit 0),
  ("refUID",.field (.var "request") "refUID"),("recipient",.field (.var "request") "recipient"),
  ("attester",.var "attester"),("revocable",.field (.var "request") "revocable"),("data",.field (.var "request") "data")]
def newAttestationBody : Body := [
  .letDecl "attestation" (some attestationABI) newAttestationExpr,
  .letDecl "uid" (some abiBytes32) (.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE ⟨0⟩)),
  .letDecl "bump" (some (.elem (.int (.uint ⟨32,by decide⟩)))) (.intLit 0)]
def newAttestationLocals (L : Store) (a : AttestationRecord) : Store :=
  ((L.insert "attestation" a.value).insert "uid" (wordBytes32Value ⟨0⟩)).insert "bump" (.int 0)

theorem newAttestationExpr_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {r : AttestationRequestRecord}
    {schema time : UInt256} {attester : AccountAddress}
    (hr : frame.locals.get? "request" = some r.struct)
    (hs : frame.locals.get? "schema" = some (wordBytes32Value schema))
    (ht : frame.locals.get? "__c2" = some (.int (Int.ofNat time.toNat)))
    (ha : frame.locals.get? "attester" = some (.address attester)) :
    evalExpr? cfg frame evm newAttestationExpr = .ok (newAttestation r schema time attester).value := by
  simp only [newAttestationExpr,evalExpr?,evalStructFields?,hr,hs,ht,ha,EvalResult.ofOption,EvalResult.bind,bind,pure,
    AttestationRequestRecord.struct,lookupField?]
  rfl

theorem newAttestationSource {L imms : Store} {evm : EVM.State} {r : AttestationRequestRecord}
    {schema time : UInt256} {attester : AccountAddress}
    (hr : L.get? "request" = some r.struct) (hs : L.get? "schema" = some (wordBytes32Value schema))
    (ht : L.get? "__c2" = some (.int (Int.ofNat time.toNat))) (ha : L.get? "attester" = some (.address attester)) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm newAttestationBody
      (.ok {contract := contract,locals := newAttestationLocals L (newAttestation r schema time attester),immutables := imms} evm) := by
  exact ExecBlock.consNormal (ExecStmt.letDecl (newAttestationExpr_eval hr hs ht ha))
    (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,wordBytes32Value,pure]))
      (ExecBlock.consNormal (ExecStmt.letDecl (by simp only [evalExpr?,pure])) ExecBlock.nil))

theorem newAttestationLocals_uid {L : Store} {a : AttestationRecord} {heap : Nat}
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) (hd : L.get? "_db" = none) :
    UIDLoopLocals (newAttestationLocals L a) a ⟨0⟩ heap := by
  refine ⟨?_,?_,?_,⟨wordBytes32Value ⟨0⟩,?_⟩,?_⟩
  · simp only [newAttestationLocals,store_get_ne _ _ (by decide : ("bump" == "attestation") = false),
      store_get_ne _ _ (by decide : ("uid" == "attestation") = false),store_get_self]
  · exact store_get_self _ _ (.int 0)
  · simpa only [newAttestationLocals,store_get_ne _ _ (by decide : ("bump" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("uid" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("attestation" == "$EAS.freeMemory") = false)] using hh
  · simp only [newAttestationLocals,store_get_ne _ _ (by decide : ("bump" == "uid") = false),store_get_self]
  · simpa only [newAttestationLocals,store_get_ne _ _ (by decide : ("bump" == "_db") = false),
      store_get_ne _ _ (by decide : ("uid" == "_db") = false),
      store_get_ne _ _ (by decide : ("attestation" == "_db") = false)] using hd

end Benchmarks.EAS.EAS
