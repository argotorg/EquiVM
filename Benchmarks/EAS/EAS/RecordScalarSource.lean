import Benchmarks.EAS.EAS.AttestationWriteStatements

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def recordSetUIDStmt : Stmt :=
  .assign .localVar {base := "attestation",steps := [.field "uid"]} (.var "uid")
def recordScalarLocals (L : Store) (a : AttestationRecord) (word : UInt256) : Store :=
  L.insert "attestation" {a with uid := word}.value
def recordScalarBody : Body := recordSetUIDStmt ::
  (["uid","schema","time","expirationTime","revocationTime","refUID","recipient","attester","revocable"].map attestationWriteStmt)

theorem recordSetUIDSource {L imms : Store} {evm : EVM.State} {a : AttestationRecord} {word : UInt256}
    (ha : L.get? "attestation" = some a.value) (hu : L.get? "uid" = some (wordBytes32Value word)) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm recordSetUIDStmt
      (.ok {contract := contract,locals := recordScalarLocals L a word,immutables := imms} evm) := by
  apply ExecStmt.assign (hperm := Or.inl rfl) (value := wordBytes32Value word) (by simp only [evalExpr?,hu,EvalResult.ofOption])
  simp only [recordSetUIDStmt,assignStorageRef?,ha,updateLocalPath?,
    show lookupField? a.value "uid" = some (wordBytes32Value a.uid) from rfl,EvalResult.ofOption,EvalResult.bind,bind,pure,
    show updateField? a.value "uid" (wordBytes32Value word) = some {a with uid := word}.value from rfl]
  rfl

theorem recordScalarLocals_attestation (L : Store) (a : AttestationRecord) (word : UInt256) :
    (recordScalarLocals L a word).get? "attestation" = some {a with uid := word}.value := store_get_self _ _ _

theorem recordScalarLocals_get (L : Store) (a : AttestationRecord) (word : UInt256) (name : Ident)
    (h : ("attestation" == name) = false) : (recordScalarLocals L a word).get? name = L.get? name := store_get_ne _ _ h

theorem recordScalarSource {L imms : Store} {evm : EVM.State} {a : AttestationRecord} {word : UInt256}
    (ha : L.get? "attestation" = some a.value) (hu : L.get? "uid" = some (wordBytes32Value word))
    (hd : L.get? "_db" = none)
    (hperm : evm.executionEnv.perm = true) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm recordScalarBody
      (.ok {contract := contract,locals := recordScalarLocals L a word,immutables := imms}
        (attestationWriteHead evm (dbSlot word) {a with uid := word})) := by
  apply ExecBlock.consNormal (recordSetUIDSource ha hu)
  have hd' : (recordScalarLocals L a word).get? "_db" = none :=
    (recordScalarLocals_get _ _ _ _ (by decide)).trans hd
  have hu' : (recordScalarLocals L a word).get? "uid" = some (wordBytes32Value word) :=
    (recordScalarLocals_get _ _ _ _ (by decide)).trans hu
  exact attestationScalarAssignmentsRun (hperm := by assumption) hd' hu' (recordScalarLocals_attestation _ _ _)
    (attestationScalarWrites (dbSlot word) {a with uid := word}) (fun _ h => h)

theorem recordScalarSource_static {L imms : Store} {evm : EVM.State} {a : AttestationRecord} {word : UInt256}
    (ha : L.get? "attestation" = some a.value) (hu : L.get? "uid" = some (wordBytes32Value word))
    (hd : L.get? "_db" = none) (hp : evm.executionEnv.perm = false) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm recordScalarBody .staticViolation := by
  apply ExecBlock.consNormal (recordSetUIDSource ha hu)
  apply attestationWriteStatic
    ((recordScalarLocals_get L a word "_db" (by decide)).trans hd)
    ((recordScalarLocals_get L a word "uid" (by decide)).trans hu)
    (recordScalarLocals_attestation L a word) hp

end Benchmarks.EAS.EAS
