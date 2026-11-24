import Benchmarks.EAS.EAS.ResolverOneSource
import Benchmarks.EAS.EAS.StaticCallBridge
import Benchmarks.EAS.EAS.BytesAllocation

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open Benchmarks.EAS.EAS.Immutables
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure SchemaRecord where
  uid : UInt256
  resolver : AccountAddress
  revocable : Bool
  schema : ByteArray

def SchemaRecord.tuple (a : SchemaRecord) : Value :=
  .tuple [wordBytes32Value a.uid, .address a.resolver, .bool a.revocable, .bytes a.schema]
def SchemaRecord.value (a : SchemaRecord) : Value :=
  .struct "SchemaRecord" [("uid",wordBytes32Value a.uid), ("resolver",.address a.resolver),
    ("revocable",.bool a.revocable), ("schema",.bytes a.schema)]
def schemaRecordABI : ABIType := .tuple [abiBytes32, .elem .address, .elem .bool, .string]

def getSchemaPayload (uid : UInt256) : ByteArray :=
  selectorBytes 0xa2 0xea 0x7c 0x6e ++ uid.toByteArray
def getSchemaPayloadExpr : Expr := .abiEncodePacked [
  (.elem (.bytes ⟨3,by decide⟩), .fixedBytesLit ⟨3,by decide⟩ [0xa2,0xea,0x7c,0x6e]),
  (abiBytes32,.var "uid")]
def getSchemaPrefix : Body := [
  .letDecl "registry" (some (.elem .address)) (.immutable "_schemaRegistry"),
  .letDecl "payload" (some .bytes) getSchemaPayloadExpr,
  .lowLevelCall (.var "registry") (.intLit 0) (.var "payload") "ok" "result" false]
def getSchemaDecode : Body := [
  .letDecl "record" none (.abiDecode schemaRecordABI (.var "result")),
  .letDecl "text" (some .string) (.tupleGet (.var "record") 3),
  .require (.binary .le (.arrayLength .localVar {base := "text"}) (.intLit (2^64-1)))]
def getSchemaReturn : Body := [
  .return [.structLit "SchemaRecord" [("uid",.tupleGet (.var "record") 0),
    ("resolver",.tupleGet (.var "record") 1), ("revocable",.tupleGet (.var "record") 2),
    ("schema",.tupleGet (.var "record") 3)], .var "$EAS.freeMemory"],
  .return [.tupleLit [],.var "$EAS.freeMemory"]]
def getSchemaSuffix : Body := [.require (.var "ok")] ++
  allocateBlock (.arrayLength .localVar {base := "result"}) ++ allocateBlock (.intLit 128) ++
  getSchemaDecode ++ allocateBlock (bytesAllocationExpr (.arrayLength .localVar {base := "text"})) ++ getSchemaReturn
abbrev getSchemaFunction : FunctionDecl := contract.functions[9]!
theorem getSchema_body : getSchemaFunction.body = getSchemaPrefix ++ getSchemaSuffix := by native_decide

theorem getSchemaPayload_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {uid : UInt256}
    (hu : frame.locals.get? "uid" = some (wordBytes32Value uid)) :
    evalExpr? cfg frame evm getSchemaPayloadExpr = .ok (.bytes (getSchemaPayload uid)) := by
  have he : evalPackedArgs? cfg frame evm [
      (.elem (.bytes ⟨3,by decide⟩), .fixedBytesLit ⟨3,by decide⟩ [0xa2,0xea,0x7c,0x6e]),
      (abiBytes32,.var "uid")] = .ok ([0xa2,0xea,0x7c,0x6e] ++ EVM.Word.toBytesBE uid) := by
    apply evalPackedArgs_cons (v := .fixedBytes ⟨3,by decide⟩ [0xa2,0xea,0x7c,0x6e])
      (by simp only [evalExpr?, pure]) (by rfl)
    exact evalPackedArgs_single (by simp only [evalExpr?, hu, EvalResult.ofOption]) (encodePacked_bytes32 uid)
  simp only [getSchemaPayloadExpr, evalExpr?, he, EvalResult.bind, bind, pure]
  apply congrArg (fun b => EvalResult.ok (Value.bytes b))
  apply byteArray_eq_of_toList_eq
  simp only [getSchemaPayload, byteArray_toList_eq, ByteArray.data_append, Array.toList_append,
    List.toList_toArray, toByteArray_eq_toBytesBE]
  rfl

def getSchemaPrefixLocals (locals : Store) (v : EASImmutables) (uid : UInt256) (success : Bool) (out : ByteArray) : Store :=
  locals |>.insert "registry" (.address v._schemaRegistry) |>.insert "payload" (.bytes (getSchemaPayload uid))
    |>.insert "ok" (.bool success) |>.insert "result" (.bytes out)

theorem getSchemaPrefixSource {cfg : Config} {locals : Store} {evm evm' : EVM.State}
    {uid : UInt256} {success : Bool} {out : ByteArray} (v : EASImmutables)
    (hu : locals.get? "uid" = some (wordBytes32Value uid))
    (hc : callViaEVM fork evm v._schemaRegistry 0 (getSchemaPayload uid) (success,evm',out) false) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := immStore v} evm getSchemaPrefix
      (.ok {contract := contract, locals := getSchemaPrefixLocals locals v uid success out, immutables := immStore v} evm') := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (evalImmutable__schemaRegistry _ _ _ _ v))
  apply ExecBlock.consNormal (ExecStmt.letDecl (getSchemaPayload_eval (by
    simpa only [store_get_ne _ _ (by decide : ("registry" == "uid") = false)] using hu)))
  apply ExecBlock.consNormal (lowLevelCallSource_perm (fork := fork) (hperm := Or.inl rfl) ?_ (by simp only [evalExpr?, pure]) ?_ hc) ExecBlock.nil
  · simp only [evalExpr?, store_get_ne _ _ (by decide : ("payload" == "registry") = false), store_get_self, EvalResult.ofOption]
  · simp only [evalExpr?, store_get_self, EvalResult.ofOption]

end Benchmarks.EAS.EAS
