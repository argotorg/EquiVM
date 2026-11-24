import Benchmarks.EAS.EAS.RevocationRequest
import Benchmarks.EAS.EAS.RevokeGuards
import Benchmarks.EAS.EAS.AttestSchemaSource
import Benchmarks.EAS.EAS.ArrayLoopSource

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

abbrev revokeFunction : FunctionDecl := contract.functions[17]!
def revokeReadRequest : Body := heapResultBlock "_decodeRevocationData"
  [.index (.var "data") (.var "i"),.var "$EAS.freeMemory"] "request$allocation" "request" "$EAS.freeMemory"
def revokeBindAlias : Stmt := .letStorage "attestation" {base := "_db",steps := [.mindex (.field (.var "request") "uid")]}
def revokeWriteTime : Stmt := .assign .storage (attestationAliasRef "revocationTime") (.var "__c1")
def revokeCopyArgs : List Expr := [.field (.var "request") "uid",.var "$EAS.freeMemory"]
def revokeCopyBody : Body := heapResultBlock "_copyStoredAttestation" revokeCopyArgs "copied$allocation" "copied" "$EAS.freeMemory"
def revokeUpdateBody : Body := [
  .assign .localVar {base := "attestations",steps := [.aindex (.var "i")]} (.var "copied"),
  .assign .localVar {base := "values",steps := [.aindex (.var "i")]} (.field (.var "request") "value"),
  .emit "Revoked" [.storage (attestationAliasRef "recipient"),.var "revoker",.field (.var "request") "uid",.storage (attestationAliasRef "schema")],
  localCastIncrement "i"]
def revokeIteration : Body := revokeReadRequest ++ [revokeBindAlias] ++ revokeGuards ++
  readTimeBlock "__c1$allocation" "__c1" ++ [revokeWriteTime] ++ revokeCopyBody ++ revokeUpdateBody
def revokeLoop : Stmt := .while timeArrayGuard revokeIteration
def revokeResolveArgs : List Expr := [.var "schemaRecord",.var "attestations",.var "values",
  .boolLit true,.var "availableValue",.var "last",.var "$EAS.freeMemory"]
def revokeFinish : Body := heapResultBlock "_resolveAttestations" revokeResolveArgs "__c2$allocation" "__c2" "$EAS.freeMemory" ++
  [.return [.var "__c2",.var "$EAS.freeMemory"],.return [.tupleLit [],.var "$EAS.freeMemory"]]
def revokeLengthDecl : Stmt := .letDecl "length" (some abiUInt256) (.arrayLength .localVar {base := "data"})

theorem revoke_body : revokeFunction.body = attestSchemaBody ++ [schemaUIDStmt,revokeLengthDecl] ++
    attestArraysBody ++ [revokeLoop] ++ revokeFinish := by native_decide

def revokeRequestLocals (L : Store) (r : RevocationRequestRecord) (heap : Nat) : Store :=
  heapResultLocals L "request$allocation" "request" "$EAS.freeMemory" r.struct heap
def revokeAliasLocals (L : Store) (word : UInt256) : Store :=
  L.insert "attestation" (.storageRef (attestationER word) attestationType)

theorem revokeRequestField_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {r : RevocationRequestRecord}
    (hr : frame.locals.get? "request" = some r.struct) (field : Ident) (value : Value)
    (hv : lookupField? r.struct field = some value) :
    evalExpr? cfg frame evm (.field (.var "request") field) = .ok value := by
  simp only [evalExpr?,hr,EvalResult.ofOption,EvalResult.bind,bind]
  change EvalResult.ofOption .typeError (lookupField? r.struct field) = _
  rw [hv]; rfl

theorem revokeReadRequest_source {L imms : Store} {evm : EVM.State} {rs : List RevocationRequestRecord} {i heap : Nat}
    (hd : L.get? "data" = some (.array (rs.map RevocationRequestRecord.tuple)))
    (hi : L.get? "i" = some (.int (Int.ofNat i))) (hb : i < rs.length)
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm revokeReadRequest
      (.ok {contract := contract,locals := revokeRequestLocals L rs[i] heap,immutables := imms} evm) := by
  apply heapResultBlock_ok (decodeRevocationDataCall (r := rs[i]) (heap := heap) ?_) hh (by decide) (by decide) (by decide)
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm
      (.index (.var "data") (.var "i")) = .ok rs[i].tuple := by
    have hw : lookupNth? rs i = some rs[i] := by rw [lookupNth_getElem,List.getElem?_eq_getElem hb]
    simp only [evalExpr?,hd,hi,EvalResult.ofOption,EvalResult.bind,bind,pure,evalIndex?,Int.ofNat_eq_natCast,
      Int.natCast_nonneg,List.length_map,Nat.cast_lt,hb,and_self,if_true,Int.toNat_natCast,lookupNth_map,hw,
      Option.map_some,RevocationRequestRecord.tuple,normalizeRawBoolWord?]
  simp only [evalExprs?,he,evalExpr?,hh,EvalResult.ofOption,EvalResult.bind,bind,pure]

theorem revokeBindAlias_source {L imms : Store} {evm : EVM.State} {r : RevocationRequestRecord}
    (hd : L.get? "_db" = none) (hr : L.get? "request" = some r.struct) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm revokeBindAlias
      (.ok {contract := contract,locals := revokeAliasLocals L r.uid,immutables := imms} evm) :=
  ExecStmt.letStorage (attestationRoot_resolve hd (revokeRequestField_eval hr "uid" _ rfl))

theorem revokeWriteTime_source {L imms : Store} {evm : EVM.State} {word time : UInt256}
    (ha : L.get? "attestation" = some (.storageRef (attestationER word) attestationType))
    (ht : L.get? "__c1" = some (.int (Int.ofNat time.toNat))) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm revokeWriteTime
      (if evm.executionEnv.perm then .ok {contract := contract,locals := L,immutables := imms} ((revokeTimeField word time).apply evm) else .staticViolation) :=
  execStmt_assign_storage (evalLocalValue ht) (attestationAlias_writeTime ha)

theorem revokeWriteTime_static {L imms : Store} {evm : EVM.State} {word time : UInt256}
    (ha : L.get? "attestation" = some (.storageRef (attestationER word) attestationType))
    (ht : L.get? "__c1" = some (.int (Int.ofNat time.toNat))) (hp : evm.executionEnv.perm = false) :
    ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm revokeWriteTime .staticViolation :=
  execStmt_assign_static (revokeWriteTime_source ha ht) hp

end Benchmarks.EAS.EAS
