import Benchmarks.EAS.EAS.VerifyDigest
import Benchmarks.EAS.EAS.NonceSource
import Benchmarks.EAS.EAS.RevocationRequestMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure DelegatedRevocationRecord where
  schema : UInt256
  data : RevocationRequestRecord
  signature : SignatureRecord
  revoker : AccountAddress

def DelegatedRevocationRecord.tuple (r : DelegatedRevocationRecord) : Value :=
  .tuple [wordBytes32Value r.schema,r.data.tuple,r.signature.tuple,.address r.revoker]
def DelegatedRevocationRecord.struct (r : DelegatedRevocationRecord) : Value :=
  .struct "DelegatedRevocationRequest" [("schema",wordBytes32Value r.schema),("data",r.data.tuple),
    ("signature",r.signature.tuple),("revoker",.address r.revoker)]

theorem delegatedRevokeField {cfg : Config} {frame : Frame} {evm : EVM.State}
    {r : DelegatedRevocationRecord} (h : frame.locals.get? "request" = some r.struct)
    (field : Ident) (value : Value) (hf : lookupField? r.struct field = some value) :
    evalExpr? cfg frame evm (.field (.var "request") field) = .ok value :=
  evalRecordField (by simp only [evalExpr?,h,EvalResult.ofOption]) hf

abbrev verifyRevokeFunction : FunctionDecl := contract.functions[18]!
def verifyRevokeDecode : Body :=
  heapResultBlock "_decodeRevocationData" [.field (.var "request") "data",.var "$EAS.freeMemory"]
    "data$allocation" "data" "$EAS.freeMemory" ++
  heapResultBlock "_decodeSignature" [.field (.var "request") "signature",.var "$EAS.freeMemory"]
    "signature$allocation" "signature" "$EAS.freeMemory"
def verifyRevokeRead : Body := verifyRevokeDecode ++ nonceReadBlock (.field (.var "request") "revoker")
def revokeTypeHash : UInt256 := ⟨76690012066023820863223560235467895628960054969079040944716494920993861113424⟩
def verifyRevokeWords (r : DelegatedRevocationRecord) (nonce : UInt256) : List UInt256 :=
  [revokeTypeHash,r.schema,r.data.uid,nonce]
def verifyRevokePayload (r : DelegatedRevocationRecord) (nonce : UInt256) : ByteArray := wordBytes (verifyRevokeWords r nonce)
def verifyRevokeHash (r : DelegatedRevocationRecord) (nonce : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (verifyRevokePayload r nonce))
def verifyRevokePayloadExpr : Expr := .abiEncodePacked [
  (abiBytes32,.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE revokeTypeHash)),
  (abiBytes32,.field (.var "request") "schema"),(abiBytes32,.field (.var "data") "uid"),(abiUInt256,.var "nonce")]
def verifyRevokeHashBody : Body := [
  .letDecl "payload" (some .bytes) verifyRevokePayloadExpr,
  .letDecl "structHash" (some abiBytes32) (.keccak256 (.var "payload"))]
theorem verifyRevoke_body : verifyRevokeFunction.body = verifyRevokeRead ++
    [nonceWrite (.field (.var "request") "revoker")] ++ allocateBlock (.intLit 160) ++
    verifyRevokeHashBody ++ verifyDigestBody "revoker" := by native_decide

def verifyRevokeDataLocals (L : Store) (r : DelegatedRevocationRecord) (heap : Nat) : Store :=
  heapResultLocals L "data$allocation" "data" "$EAS.freeMemory" r.data.struct heap
def verifyRevokeDecodeLocals (L : Store) (r : DelegatedRevocationRecord) (heap : Nat) : Store :=
  heapResultLocals (verifyRevokeDataLocals L r heap) "signature$allocation" "signature" "$EAS.freeMemory" r.signature.struct heap
def verifyRevokeReadLocals (L : Store) (r : DelegatedRevocationRecord) (nonce : UInt256) (heap : Nat) : Store :=
  nonceLocals (verifyRevokeDecodeLocals L r heap) nonce

theorem verifyRevokeReadSource {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationRecord} {heap : Nat}
    (hreq : L.get? "request" = some r.struct) (hn : L.get? "_nonces" = none)
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm verifyRevokeRead
      (.ok {contract := contract,locals := verifyRevokeReadLocals L r (nonceWord evm r.revoker) heap,immutables := imms} evm) := by
  have hdata := decodeRevocationDataCall (fork := fork) (retVar := "data$allocation") (r := r.data) (heap := heap)
    (show evalExprs? config {contract := contract,locals := L,immutables := imms} evm
      [.field (.var "request") "data",.var "$EAS.freeMemory"] = .ok [r.data.tuple,.int (Int.ofNat heap)] by
      simp only [evalExprs?,delegatedRevokeField (frame := {contract := contract,locals := L,immutables := imms}) hreq "data" _ rfl,evalExpr?,hf,EvalResult.ofOption,EvalResult.bind,bind,pure])
  have hp1 := heapResultBlock_ok (result := "data") hdata hf (by decide) (by decide) (by decide)
  have hreq1 : (verifyRevokeDataLocals L r heap).get? "request" = some r.struct :=
    (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hreq
  have hf1 : (verifyRevokeDataLocals L r heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) :=
    heapResultLocals_heap _ _ _ _ _ _
  have hsig := decodeSignatureCall (fork := fork) (retVar := "signature$allocation") (s := r.signature) (heap := heap)
    (show evalExprs? config {contract := contract,locals := verifyRevokeDataLocals L r heap,immutables := imms} evm
      [.field (.var "request") "signature",.var "$EAS.freeMemory"] = .ok [r.signature.tuple,.int (Int.ofNat heap)] by
      simp only [evalExprs?,delegatedRevokeField (frame := {contract := contract,locals := verifyRevokeDataLocals L r heap,immutables := imms}) hreq1 "signature" _ rfl,evalExpr?,hf1,EvalResult.ofOption,EvalResult.bind,bind,pure])
  have hp2 := heapResultBlock_ok (result := "signature") hsig hf1 (by decide) (by decide) (by decide)
  have hn2 : (verifyRevokeDecodeLocals L r heap).get? "_nonces" = none := by
    simpa (disch := decide) only [verifyRevokeDecodeLocals,verifyRevokeDataLocals,heapResultLocals,unpackHeapLocals,store_get_ne] using hn
  have hreq2 : ((verifyRevokeDecodeLocals L r heap).insert "nonce" (.int 0)).get? "request" = some r.struct := by
    simpa (disch := decide) only [verifyRevokeDecodeLocals,verifyRevokeDataLocals,heapResultLocals,unpackHeapLocals,store_get_ne] using hreq
  have hp3 := nonceReadSource (fork := fork) hn2 (delegatedRevokeField (evm := evm) (frame := {contract := contract,locals := (verifyRevokeDecodeLocals L r heap).insert "nonce" (.int 0),immutables := imms}) hreq2 "revoker" _ rfl)
  exact execBlock_append (execBlock_append hp1 hp2) hp3

theorem verifyRevokeReadLocals_facts {L : Store} {r : DelegatedRevocationRecord} {nonce : UInt256} {heap : Nat}
    (hreq : L.get? "request" = some r.struct) (hn : L.get? "_nonces" = none) :
    (verifyRevokeReadLocals L r nonce heap).get? "request" = some r.struct ∧
    (verifyRevokeReadLocals L r nonce heap).get? "data" = some r.data.struct ∧
    (verifyRevokeReadLocals L r nonce heap).get? "signature" = some r.signature.struct ∧
    (verifyRevokeReadLocals L r nonce heap).get? "nonce" = some (.int (Int.ofNat nonce.toNat)) ∧
    (verifyRevokeReadLocals L r nonce heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) ∧
    (verifyRevokeReadLocals L r nonce heap).get? "_nonces" = none := by
  simp (disch := decide) only [verifyRevokeReadLocals,nonceLocals,verifyRevokeDecodeLocals,verifyRevokeDataLocals,
    heapResultLocals,unpackHeapLocals,store_get_ne,store_get_self,hreq,hn,and_self]

theorem verifyRevokePayload_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {r : DelegatedRevocationRecord} {nonce : UInt256}
    (hreq : frame.locals.get? "request" = some r.struct) (hd : frame.locals.get? "data" = some r.data.struct)
    (hn : frame.locals.get? "nonce" = some (.int (Int.ofNat nonce.toNat))) :
    evalExpr? cfg frame evm verifyRevokePayloadExpr = .ok (.bytes (verifyRevokePayload r nonce)) := by
  apply evalPackedBytes
  simp only [verifyRevokePayload,verifyRevokeWords,wordBytes_eq_list,byteArray_toList_eq,List.toList_data_toByteArray,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]
  apply evalPackedArgs_cons (v := wordBytes32Value revokeTypeHash) (by simp only [evalExpr?,pure]) (encodePacked_bytes32 _)
  apply evalPackedArgs_cons (delegatedRevokeField hreq "schema" _ rfl) (encodePacked_bytes32 _)
  apply evalPackedArgs_cons (evalRecordField (record := r.data.struct) (by simp only [evalExpr?,hd,EvalResult.ofOption]) (field := "uid") (by rfl)) (encodePacked_bytes32 _)
  exact evalPackedArgs_single (by simp only [evalExpr?,hn,EvalResult.ofOption]) (encodePacked_uint256 _)

def verifyRevokeHashLocals (L : Store) (r : DelegatedRevocationRecord) (nonce : UInt256) : Store :=
  (L.insert "payload" (.bytes (verifyRevokePayload r nonce))).insert "structHash" (wordBytes32Value (verifyRevokeHash r nonce))

theorem verifyRevokeHashSource {L imms : Store} {evm : EVM.State} {r : DelegatedRevocationRecord} {nonce : UInt256}
    (hreq : L.get? "request" = some r.struct) (hd : L.get? "data" = some r.data.struct)
    (hn : L.get? "nonce" = some (.int (Int.ofNat nonce.toNat))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm verifyRevokeHashBody
      (.ok {contract := contract,locals := verifyRevokeHashLocals L r nonce,immutables := imms} evm) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (verifyRevokePayload_eval hreq hd hn)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := wordBytes32Value (verifyRevokeHash r nonce)) ?_) ExecBlock.nil
  simp only [evalExpr?,store_get_self,EvalResult.ofOption,EvalResult.bind,bind,pure,verifyRevokeHash,
    wordBytes32Value,toBytesBE_keccak_uInt256OfByteArray]
  rfl

end Benchmarks.EAS.EAS
