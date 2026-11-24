import Benchmarks.EAS.EAS.RevokeSetup

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def revokeArgs (schema : UInt256) (rs : List RevocationRequestRecord) (revoker : AccountAddress)
    (available : UInt256) (last : Bool) (heap : Nat) : Store :=
  (∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap)) |>.insert "last" (.bool last)
    |>.insert "availableValue" (.int (Int.ofNat available.toNat)) |>.insert "revoker" (.address revoker)
    |>.insert "data" (.array (rs.map RevocationRequestRecord.tuple)) |>.insert "schema" (wordBytes32Value schema)

theorem revoke_lookup : lookupCallable? contract "_revoke" = some revokeFunction.toCallable := rfl

theorem revoke_bind (schema : UInt256) (rs : List RevocationRequestRecord) (revoker : AccountAddress)
    (available : UInt256) (last : Bool) (heap : Nat) :
    bindParams? revokeFunction.params [wordBytes32Value schema,.array (rs.map RevocationRequestRecord.tuple),
      .address revoker,.int (Int.ofNat available.toNat),.bool last,.int (Int.ofNat heap)] =
      some (revokeArgs schema rs revoker available last heap) := rfl

theorem revokeLengthSource {cfg : Config} {L imms : Store} {evm : EVM.State} {rs : List RevocationRequestRecord}
    (hd : L.get? "data" = some (.array (rs.map RevocationRequestRecord.tuple))) :
    ExecStmt fork cfg {contract := contract,locals := L,immutables := imms} evm revokeLengthDecl
      (.ok {contract := contract,locals := L.insert "length" (.int (Int.ofNat rs.length)),immutables := imms} evm) := by
  apply ExecStmt.letDecl
  simpa only [List.length_map] using evalLocalArrayLength (cfg := cfg) (stele := {contract := contract,locals := L,immutables := imms}) (evm := evm) hd

theorem revokeSetupLocals_of_schema (site : RevokeSite) (rs : List RevocationRequestRecord) (s : SchemaRecord) (initial : Nat) :
    RevokeSetupLocals ((attestSchemaLocals (revokeArgs site.schema rs site.revoker site.available site.last initial)
      s site.records.toNat).insert "length" (.int (Int.ofNat rs.length))) site rs s site.records.toNat := by
  constructor <;>
    simp (disch := decide) only [attestSchemaLocals,heapResultLocals,unpackHeapLocals,revokeArgs,
      store_get_ne,store_get_self,store_get_empty]

end Benchmarks.EAS.EAS
