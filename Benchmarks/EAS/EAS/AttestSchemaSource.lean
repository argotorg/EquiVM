import Benchmarks.EAS.EAS.AttestInitialSource
import Benchmarks.EAS.EAS.AttestFromSchema

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS

def attestSchemaArgs : List Expr := [.var "schema",.var "$EAS.freeMemory"]
def attestSchemaBody : Body := heapResultBlock "_getSchema" attestSchemaArgs "schemaRecord$allocation" "schemaRecord" "$EAS.freeMemory"
def attestSchemaLocals (L : Store) (s : SchemaRecord) (heap : Nat) : Store :=
  heapResultLocals L "schemaRecord$allocation" "schemaRecord" "$EAS.freeMemory" s.value heap

theorem attest_body : attestFunction.body = attestInitialBody ++ attestSchemaBody ++ attestFromSchemaBody := by native_decide

theorem attestSchemaSource {L imms : Store} {evm evm' : EVM.State} {s : SchemaRecord} {old heap : Nat}
    (hh : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat old)))
    (hc : ExecStmt fork config {contract := contract,locals := L,immutables := imms} evm
      (.internalCall "_getSchema" attestSchemaArgs "schemaRecord$allocation")
      (.ok (resumeAfterInternalCall {contract := contract,locals := L,immutables := imms}
        "schemaRecord$allocation" (some [s.value,.int (Int.ofNat heap)])) evm')) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm attestSchemaBody
      (.ok {contract := contract,locals := attestSchemaLocals L s heap,immutables := imms} evm') :=
  heapResultBlock_ok hc hh (by decide) (by decide) (by decide)

theorem attestSchemaLocals_view (schema : UInt256) (rs : List AttestationRequestRecord) (attester : AccountAddress)
    (available : UInt256) (last : Bool) (heap first next : Nat) (s : SchemaRecord) (schemaHeap : Nat) :
    AttestSetupLocals (attestSchemaLocals (attestInitialLocals (attestArgs schema rs attester available last heap)
      rs.length first next) s schemaHeap) rs s schema attester available last schemaHeap := by
  constructor <;>
    simp (disch := decide) only [attestSchemaLocals,heapResultLocals,unpackHeapLocals,
      attestInitialLocals,attestDeclaredLocals,allocateBlockLocals,attestArgs,store_get_ne,store_get_self,store_get_empty]

end Benchmarks.EAS.EAS
