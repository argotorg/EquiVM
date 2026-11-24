import Benchmarks.EAS.EAS.VerifyDigest
import Benchmarks.EAS.EAS.NonceSource
import Benchmarks.EAS.EAS.RequestMemory

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

structure DelegatedAttestationRecord where
  schema : UInt256
  data : AttestationRequestRecord
  signature : SignatureRecord
  attester : AccountAddress

def DelegatedAttestationRecord.tuple (r : DelegatedAttestationRecord) : Value :=
  .tuple [wordBytes32Value r.schema,r.data.tuple,r.signature.tuple,.address r.attester]
def DelegatedAttestationRecord.struct (r : DelegatedAttestationRecord) : Value :=
  .struct "DelegatedAttestationRequest" [("schema",wordBytes32Value r.schema),("data",r.data.tuple),
    ("signature",r.signature.tuple),("attester",.address r.attester)]

theorem delegatedAttestField {cfg : Config} {frame : Frame} {evm : EVM.State}
    {r : DelegatedAttestationRecord} (h : frame.locals.get? "request" = some r.struct)
    (field : Ident) (value : Value) (hf : lookupField? r.struct field = some value) :
    evalExpr? cfg frame evm (.field (.var "request") field) = .ok value :=
  evalRecordField (by simp only [evalExpr?,h,EvalResult.ofOption]) hf

abbrev verifyAttestFunction : FunctionDecl := contract.functions[15]!
def verifyAttestDecode : Body :=
  heapResultBlock "_decodeAttestationData" [.field (.var "request") "data",.var "$EAS.freeMemory"]
    "data$allocation" "data" "$EAS.freeMemory" ++
  heapResultBlock "_decodeSignature" [.field (.var "request") "signature",.var "$EAS.freeMemory"]
    "signature$allocation" "signature" "$EAS.freeMemory"
def verifyAttestRead : Body := verifyAttestDecode ++ nonceReadBlock (.field (.var "request") "attester")
def attestTypeHash : UInt256 := ⟨99505243715942933888240952616802929847476548576208744958988217175427947486817⟩
def verifyAttestWords (r : DelegatedAttestationRecord) (nonce : UInt256) : List UInt256 :=
  [attestTypeHash,r.schema,UInt256.ofNat r.data.recipient.val,r.data.expirationTime,r.data.revocable.toUInt256,
    r.data.refUID,uInt256OfByteArray (KEC r.data.data),nonce]
def verifyAttestPayload (r : DelegatedAttestationRecord) (nonce : UInt256) : ByteArray := wordBytes (verifyAttestWords r nonce)
def verifyAttestHash (r : DelegatedAttestationRecord) (nonce : UInt256) : UInt256 :=
  uInt256OfByteArray (KEC (verifyAttestPayload r nonce))
def verifyAttestPayloadExpr : Expr := .abiEncodePacked [
  (abiBytes32,.fixedBytesLit abiBytes32Width (EVM.Word.toBytesBE attestTypeHash)),
  (abiBytes32,.field (.var "request") "schema"),
  (abiUInt256,.cast (.field (.var "data") "recipient") (.elem (.int (.uint ⟨256,by decide⟩)))),
  (abiUInt256,.field (.var "data") "expirationTime"),
  (abiUInt256,.ite (.field (.var "data") "revocable") (.intLit 1) (.intLit 0)),
  (abiBytes32,.field (.var "data") "refUID"),(abiBytes32,.var "dataHash"),(abiUInt256,.var "nonce")]
def verifyAttestHashBody : Body := [
  .letDecl "dataHash" (some abiBytes32) (.keccak256 (.field (.var "data") "data")),
  .letDecl "payload" (some .bytes) verifyAttestPayloadExpr,
  .letDecl "structHash" (some abiBytes32) (.keccak256 (.var "payload"))]
theorem verifyAttest_body : verifyAttestFunction.body = verifyAttestRead ++
    [nonceWrite (.field (.var "request") "attester")] ++ allocateBlock (.intLit 288) ++
    verifyAttestHashBody ++ verifyDigestBody "attester" := by native_decide

def verifyAttestDataLocals (L : Store) (r : DelegatedAttestationRecord) (heap : Nat) : Store :=
  heapResultLocals L "data$allocation" "data" "$EAS.freeMemory" r.data.struct heap
def verifyAttestDecodeLocals (L : Store) (r : DelegatedAttestationRecord) (heap : Nat) : Store :=
  heapResultLocals (verifyAttestDataLocals L r heap) "signature$allocation" "signature" "$EAS.freeMemory" r.signature.struct heap
def verifyAttestReadLocals (L : Store) (r : DelegatedAttestationRecord) (nonce : UInt256) (heap : Nat) : Store :=
  nonceLocals (verifyAttestDecodeLocals L r heap) nonce

theorem verifyAttestReadSource {L imms : Store} {evm : EVM.State} {r : DelegatedAttestationRecord} {heap : Nat}
    (hreq : L.get? "request" = some r.struct) (hn : L.get? "_nonces" = none)
    (hf : L.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm verifyAttestRead
      (.ok {contract := contract,locals := verifyAttestReadLocals L r (nonceWord evm r.attester) heap,immutables := imms} evm) := by
  have hdata := decodeAttestationDataCall (fork := fork) (retVar := "data$allocation") (r := r.data) (heap := heap)
    (show evalExprs? config {contract := contract,locals := L,immutables := imms} evm
      [.field (.var "request") "data",.var "$EAS.freeMemory"] = .ok [r.data.tuple,.int (Int.ofNat heap)] by
      simp only [evalExprs?,delegatedAttestField (frame := {contract := contract,locals := L,immutables := imms}) hreq "data" _ rfl,evalExpr?,hf,EvalResult.ofOption,EvalResult.bind,bind,pure])
  have hp1 := heapResultBlock_ok (result := "data") hdata hf (by decide) (by decide) (by decide)
  have hreq1 : (verifyAttestDataLocals L r heap).get? "request" = some r.struct :=
    (heapResultLocals_get _ _ _ _ _ _ _ (by decide) (by decide) (by decide)).trans hreq
  have hf1 : (verifyAttestDataLocals L r heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) :=
    heapResultLocals_heap _ _ _ _ _ _
  have hsig := decodeSignatureCall (fork := fork) (retVar := "signature$allocation") (s := r.signature) (heap := heap)
    (show evalExprs? config {contract := contract,locals := verifyAttestDataLocals L r heap,immutables := imms} evm
      [.field (.var "request") "signature",.var "$EAS.freeMemory"] = .ok [r.signature.tuple,.int (Int.ofNat heap)] by
      simp only [evalExprs?,delegatedAttestField (frame := {contract := contract,locals := verifyAttestDataLocals L r heap,immutables := imms}) hreq1 "signature" _ rfl,evalExpr?,hf1,EvalResult.ofOption,EvalResult.bind,bind,pure])
  have hp2 := heapResultBlock_ok (result := "signature") hsig hf1 (by decide) (by decide) (by decide)
  have hn2 : (verifyAttestDecodeLocals L r heap).get? "_nonces" = none := by
    simpa (disch := decide) only [verifyAttestDecodeLocals,verifyAttestDataLocals,heapResultLocals,unpackHeapLocals,store_get_ne] using hn
  have hreq2 : ((verifyAttestDecodeLocals L r heap).insert "nonce" (.int 0)).get? "request" = some r.struct := by
    simpa (disch := decide) only [verifyAttestDecodeLocals,verifyAttestDataLocals,heapResultLocals,unpackHeapLocals,store_get_ne] using hreq
  have hp3 := nonceReadSource (fork := fork) hn2 (delegatedAttestField (evm := evm) (frame := {contract := contract,locals := (verifyAttestDecodeLocals L r heap).insert "nonce" (.int 0),immutables := imms}) hreq2 "attester" _ rfl)
  exact execBlock_append (execBlock_append hp1 hp2) hp3

theorem verifyAttestReadLocals_facts {L : Store} {r : DelegatedAttestationRecord} {nonce : UInt256} {heap : Nat}
    (hreq : L.get? "request" = some r.struct) (hn : L.get? "_nonces" = none) :
    (verifyAttestReadLocals L r nonce heap).get? "request" = some r.struct ∧
    (verifyAttestReadLocals L r nonce heap).get? "data" = some r.data.struct ∧
    (verifyAttestReadLocals L r nonce heap).get? "signature" = some r.signature.struct ∧
    (verifyAttestReadLocals L r nonce heap).get? "nonce" = some (.int (Int.ofNat nonce.toNat)) ∧
    (verifyAttestReadLocals L r nonce heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) ∧
    (verifyAttestReadLocals L r nonce heap).get? "_nonces" = none := by
  simp (disch := decide) only [verifyAttestReadLocals,nonceLocals,verifyAttestDecodeLocals,verifyAttestDataLocals,
    heapResultLocals,unpackHeapLocals,store_get_ne,store_get_self,hreq,hn,and_self]

theorem verifyAttestPayload_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {r : DelegatedAttestationRecord} {nonce : UInt256}
    (hreq : frame.locals.get? "request" = some r.struct) (hd : frame.locals.get? "data" = some r.data.struct)
    (hn : frame.locals.get? "nonce" = some (.int (Int.ofNat nonce.toNat)))
    (hh : frame.locals.get? "dataHash" = some (wordBytes32Value (uInt256OfByteArray (KEC r.data.data)))) :
    evalExpr? cfg frame evm verifyAttestPayloadExpr = .ok (.bytes (verifyAttestPayload r nonce)) := by
  have hdata : evalExpr? cfg frame evm (.var "data") = .ok r.data.struct := by simp only [evalExpr?,hd,EvalResult.ofOption]
  have hb : evalExpr? cfg frame evm (.ite (.field (.var "data") "revocable") (.intLit 1) (.intLit 0)) =
      .ok (.int (Int.ofNat r.data.revocable.toUInt256.toNat)) := by
    rw [evalExpr?,evalRecordField hdata (field := "revocable") (by rfl)]
    cases r.data.revocable <;> simp only [EvalResult.bind,bind,evalExpr?,pure] <;> rfl
  apply evalPackedBytes
  simp only [verifyAttestPayload,verifyAttestWords,wordBytes_eq_list,byteArray_toList_eq,List.toList_data_toByteArray,
    List.flatMap_cons,List.flatMap_nil,List.append_nil]
  apply evalPackedArgs_cons (v := wordBytes32Value attestTypeHash) (by simp only [evalExpr?,pure]) (encodePacked_bytes32 _)
  apply evalPackedArgs_cons (delegatedAttestField hreq "schema" _ rfl) (encodePacked_bytes32 _)
  apply evalPackedArgs_cons (evalAddressAsUint256 (evalRecordField hdata (field := "recipient") (by rfl))) (encodePacked_uint256 _)
  apply evalPackedArgs_cons (evalRecordField hdata (field := "expirationTime") (by rfl)) (encodePacked_uint256 _)
  apply evalPackedArgs_cons hb (encodePacked_uint256 _)
  apply evalPackedArgs_cons (evalRecordField hdata (field := "refUID") (by rfl)) (encodePacked_bytes32 _)
  apply evalPackedArgs_cons (by simp only [evalExpr?,hh,EvalResult.ofOption]) (encodePacked_bytes32 _)
  exact evalPackedArgs_single (by simp only [evalExpr?,hn,EvalResult.ofOption]) (encodePacked_uint256 _)

def verifyAttestHashLocals (L : Store) (r : DelegatedAttestationRecord) (nonce : UInt256) : Store :=
  ((L.insert "dataHash" (wordBytes32Value (uInt256OfByteArray (KEC r.data.data)))).insert "payload" (.bytes (verifyAttestPayload r nonce))).insert "structHash" (wordBytes32Value (verifyAttestHash r nonce))

theorem verifyAttestHashSource {L imms : Store} {evm : EVM.State} {r : DelegatedAttestationRecord} {nonce : UInt256}
    (hreq : L.get? "request" = some r.struct) (hd : L.get? "data" = some r.data.struct)
    (hn : L.get? "nonce" = some (.int (Int.ofNat nonce.toNat))) :
    ExecBlock fork config {contract := contract,locals := L,immutables := imms} evm verifyAttestHashBody
      (.ok {contract := contract,locals := verifyAttestHashLocals L r nonce,immutables := imms} evm) := by
  have he : evalExpr? config {contract := contract,locals := L,immutables := imms} evm (.field (.var "data") "data") = .ok (.bytes r.data.data) :=
    evalRecordField (record := r.data.struct) (by simp only [evalExpr?,hd,EvalResult.ofOption]) (by rfl)
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := wordBytes32Value (uInt256OfByteArray (KEC r.data.data))) ?_) ?_
  · rw [evalExpr?,he]
    simp only [EvalResult.bind,bind,pure,wordBytes32Value,toBytesBE_keccak_uInt256OfByteArray]
    rfl
  have hreq' : (L.insert "dataHash" (wordBytes32Value (uInt256OfByteArray (KEC r.data.data)))).get? "request" = some r.struct :=
    (store_get_ne _ _ (by decide)).trans hreq
  have hd' : (L.insert "dataHash" (wordBytes32Value (uInt256OfByteArray (KEC r.data.data)))).get? "data" = some r.data.struct :=
    (store_get_ne _ _ (by decide)).trans hd
  have hn' : (L.insert "dataHash" (wordBytes32Value (uInt256OfByteArray (KEC r.data.data)))).get? "nonce" = some (.int (Int.ofNat nonce.toNat)) :=
    (store_get_ne _ _ (by decide)).trans hn
  refine ExecBlock.consNormal (ExecStmt.letDecl (verifyAttestPayload_eval hreq' hd' hn' (store_get_self _ _ _))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := wordBytes32Value (verifyAttestHash r nonce)) ?_) ExecBlock.nil
  simp only [evalExpr?,store_get_self,EvalResult.ofOption,EvalResult.bind,bind,pure,verifyAttestHash,
    wordBytes32Value,toBytesBE_keccak_uInt256OfByteArray]
  rfl

end Benchmarks.EAS.EAS
