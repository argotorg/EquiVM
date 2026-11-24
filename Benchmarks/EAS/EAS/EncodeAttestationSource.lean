import Benchmarks.EAS.EAS.AttestationABI
import Benchmarks.EAS.EAS.BuildDomain

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- An attestation value shared by the storage, attestation, and resolver routines.
structure AttestationRecord where
  uid : UInt256
  schema : UInt256
  time : UInt256
  expirationTime : UInt256
  revocationTime : UInt256
  refUID : UInt256
  recipient : AccountAddress
  attester : AccountAddress
  revocable : Bool
  data : ByteArray

def AttestationRecord.value (a : AttestationRecord) : Value := .struct "Attestation" [
  ("uid", wordBytes32Value a.uid), ("schema", wordBytes32Value a.schema),
  ("time", .int (Int.ofNat a.time.toNat)), ("expirationTime", .int (Int.ofNat a.expirationTime.toNat)),
  ("revocationTime", .int (Int.ofNat a.revocationTime.toNat)), ("refUID", wordBytes32Value a.refUID),
  ("recipient", .address a.recipient), ("attester", .address a.attester), ("revocable", .bool a.revocable), ("data", .bytes a.data)]

def AttestationRecord.words (a : AttestationRecord) : List UInt256 := [
  a.uid, a.schema, a.time, a.expirationTime, a.revocationTime, a.refUID,
  UInt256.ofNat a.recipient.val, UInt256.ofNat a.attester.val, a.revocable.toUInt256]

def bytesPadding (len : Nat) : Nat := (32-len%32)%32

def AttestationRecord.encoding (a : AttestationRecord) : ByteArray :=
  wordBytes (a.words ++ [⟨320⟩, UInt256.ofNat a.data.size]) ++ (a.data ++ ByteArray.zeroes (bytesPadding a.data.size))

abbrev encodeAttestationFunction : FunctionDecl := contract.functions[10]!

def encodeAttestationPadding : Expr := .newBytes
  (.binary .mod (.binary .sub (.intLit 32)
    (.binary .mod (.arrayLength .localVar {base := "data"}) (.intLit 32))) (.intLit 32))

def encodeAttestationExpr : Expr := .abiEncodePacked [
  (abiBytes32, .field (.var "attestation") "uid"), (abiBytes32, .field (.var "attestation") "schema"),
  (abiUInt256, .field (.var "attestation") "time"), (abiUInt256, .field (.var "attestation") "expirationTime"),
  (abiUInt256, .field (.var "attestation") "revocationTime"), (abiBytes32, .field (.var "attestation") "refUID"),
  (abiUInt256, .cast (.field (.var "attestation") "recipient") (.elem (.int (.uint ⟨256, by decide⟩)))),
  (abiUInt256, .cast (.field (.var "attestation") "attester") (.elem (.int (.uint ⟨256, by decide⟩)))),
  (abiUInt256, .ite (.field (.var "attestation") "revocable") (.intLit 1) (.intLit 0)),
  (abiUInt256, .intLit 320), (abiUInt256, .arrayLength .localVar {base := "data"}),
  (.bytes, .var "data"), (.bytes, .var "padding")]

theorem encodeAttestation_body : encodeAttestationFunction.body = [
    .letDecl "data" (some .bytes) (.field (.var "attestation") "data"),
    .letDecl "padding" (some .bytes) encodeAttestationPadding,
    .return [encodeAttestationExpr, .var "$EAS.freeMemory"],
    .return [.tupleLit [], .var "$EAS.freeMemory"]] := by native_decide

theorem attestationRecord_field {cfg : Config} {frame : Frame} {evm : EVM.State} {a : AttestationRecord}
    (ha : frame.locals.get? "attestation" = some a.value) (field : Ident) (value : Value)
    (hf : lookupField? a.value field = some value) :
    evalExpr? cfg frame evm (.field (.var "attestation") field) = .ok value := by
  simp only [evalExpr?, ha, EvalResult.ofOption, EvalResult.bind, bind]
  change EvalResult.ofOption .typeError (lookupField? a.value field) = _
  rw [hf]
  rfl

theorem encodeAttestationPadding_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {payload : ByteArray}
    (hd : frame.locals.get? "data" = some (.bytes payload)) :
    evalExpr? cfg frame evm encodeAttestationPadding = .ok (.bytes (ByteArray.zeroes (bytesPadding payload.size))) := by
  have hz : (32 : Int) ≠ 0 := by decide
  have hp : (32 - Int.ofNat payload.size % 32) % 32 = Int.ofNat (bytesPadding payload.size) := by
    unfold bytesPadding
    have hle : payload.size % 32 ≤ 32 := Nat.le_of_lt (Nat.mod_lt _ (by decide))
    have hm : (Int.ofNat payload.size) % 32 = Int.ofNat (payload.size%32) := (Int.natCast_emod payload.size 32).symm
    have hs : (32 : Int)-Int.ofNat (payload.size%32) = Int.ofNat (32-payload.size%32) := (Int.ofNat_sub hle).symm
    rw [hm, hs]
    exact (Int.natCast_emod (32-payload.size%32) 32).symm
  simp only [encodeAttestationPadding, evalExpr?, hd, readLocalPath?,
    EvalResult.bind, bind, pure, evalBinaryOp?, if_neg hz, hp,
    if_neg (Int.not_lt.mpr (Int.natCast_nonneg (bytesPadding payload.size)))]
  rw [ByteArray.zeroes]
  rfl


theorem encodeAttestation_eval {cfg : Config} {frame : Frame} {evm : EVM.State} {a : AttestationRecord}
    (ha : frame.locals.get? "attestation" = some a.value)
    (hd : frame.locals.get? "data" = some (.bytes a.data))
    (hp : frame.locals.get? "padding" = some (.bytes (ByteArray.zeroes (bytesPadding a.data.size))))
    (hsize : a.data.size < UInt256.size) :
    evalExpr? cfg frame evm encodeAttestationExpr = .ok (.bytes a.encoding) := by
  have hb : evalExpr? cfg frame evm (.ite (.field (.var "attestation") "revocable") (.intLit 1) (.intLit 0)) =
      .ok (.int (Int.ofNat a.revocable.toUInt256.toNat)) := by
    rw [evalExpr?, attestationRecord_field ha "revocable" (.bool a.revocable) rfl]
    cases a.revocable <;> simp only [EvalResult.bind, bind, evalExpr?, pure] <;> rfl
  have hlen : encodePackedValue? abiUInt256 (.int (Int.ofNat a.data.size)) =
      some (EVM.Word.toBytesBE (UInt256.ofNat a.data.size)) := by
    simpa only [ulit_toNat' _ hsize] using encodePacked_uint256 (UInt256.ofNat a.data.size)
  have he : evalPackedArgs? cfg frame evm [
      (abiBytes32, .field (.var "attestation") "uid"), (abiBytes32, .field (.var "attestation") "schema"),
      (abiUInt256, .field (.var "attestation") "time"), (abiUInt256, .field (.var "attestation") "expirationTime"),
      (abiUInt256, .field (.var "attestation") "revocationTime"), (abiBytes32, .field (.var "attestation") "refUID"),
      (abiUInt256, .cast (.field (.var "attestation") "recipient") (.elem (.int (.uint ⟨256, by decide⟩)))),
      (abiUInt256, .cast (.field (.var "attestation") "attester") (.elem (.int (.uint ⟨256, by decide⟩)))),
      (abiUInt256, .ite (.field (.var "attestation") "revocable") (.intLit 1) (.intLit 0)),
      (abiUInt256, .intLit 320), (abiUInt256, .arrayLength .localVar {base := "data"}),
      (.bytes, .var "data"), (.bytes, .var "padding")] =
      .ok ((a.words ++ [⟨320⟩, UInt256.ofNat a.data.size]).flatMap EVM.Word.toBytesBE ++
        (a.data.toList ++ (ByteArray.zeroes (bytesPadding a.data.size)).toList)) := by
    simp only [AttestationRecord.words, List.cons_append, List.nil_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, List.append_assoc]
    apply evalPackedArgs_cons (attestationRecord_field ha "uid" _ rfl) (encodePacked_bytes32 a.uid)
    apply evalPackedArgs_cons (attestationRecord_field ha "schema" _ rfl) (encodePacked_bytes32 a.schema)
    apply evalPackedArgs_cons (attestationRecord_field ha "time" _ rfl) (encodePacked_uint256 a.time)
    apply evalPackedArgs_cons (attestationRecord_field ha "expirationTime" _ rfl) (encodePacked_uint256 a.expirationTime)
    apply evalPackedArgs_cons (attestationRecord_field ha "revocationTime" _ rfl) (encodePacked_uint256 a.revocationTime)
    apply evalPackedArgs_cons (attestationRecord_field ha "refUID" _ rfl) (encodePacked_bytes32 a.refUID)
    apply evalPackedArgs_cons (evalAddressAsUint256 (attestationRecord_field ha "recipient" _ rfl)) (encodePacked_uint256 _)
    apply evalPackedArgs_cons (evalAddressAsUint256 (attestationRecord_field ha "attester" _ rfl)) (encodePacked_uint256 _)
    apply evalPackedArgs_cons hb (encodePacked_uint256 _)
    apply evalPackedArgs_cons (by simp only [evalExpr?, pure]; rfl) (encodePacked_uint256 (UInt256.ofNat 320))
    apply evalPackedArgs_cons (by simp only [evalExpr?, hd, readLocalPath?, EvalResult.bind, bind, pure]) hlen
    apply evalPackedArgs_cons (by simp only [evalExpr?, hd, EvalResult.ofOption]) (encodePacked_dynamic_bytes _)
    exact evalPackedArgs_single (by simp only [evalExpr?, hp, EvalResult.ofOption]) (encodePacked_dynamic_bytes _)
  simp only [encodeAttestationExpr, evalExpr?, he, EvalResult.bind, bind, pure]
  apply congrArg (fun b => EvalResult.ok (Value.bytes b))
  apply byteArray_eq_of_toList_eq
  simp only [AttestationRecord.encoding, AttestationRecord.words, wordBytes, List.cons_append, List.nil_append,
    List.flatMap_cons, List.flatMap_nil, List.append_nil, List.append_assoc, byteArray_toList_eq,
    ByteArray.data_append, Array.toList_append, List.toList_toArray, toByteArray_eq_toBytesBE,
    ByteArray.empty, ByteArray.emptyWithCapacity, Array.toList_empty, List.nil_append]
  rfl


def encodeAttestationLocals (locals : Store) (a : AttestationRecord) : Store :=
  (locals.insert "data" (.bytes a.data)).insert "padding" (.bytes (ByteArray.zeroes (bytesPadding a.data.size)))

theorem encodeAttestationSource {cfg : Config} {evm : EVM.State} {locals imms : Store}
    {a : AttestationRecord} {heap : Nat}
    (ha : locals.get? "attestation" = some a.value)
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hsize : a.data.size < UInt256.size) :
    ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm encodeAttestationFunction.body
      (.returned {contract := contract, locals := encodeAttestationLocals locals a, immutables := imms}
        evm (some [.bytes a.encoding, .int (Int.ofNat heap)])) := by
  rw [encodeAttestation_body]
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal (ExecStmt.letDecl (attestationRecord_field ha "data" (.bytes a.data) rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (encodeAttestationPadding_eval (store_get_self _ _ _)))
  apply ExecBlock.consReturn
  apply ExecStmt.return
  have ha' : (encodeAttestationLocals locals a).get? "attestation" = some a.value := by
    simp only [encodeAttestationLocals, store_get_ne _ _ (by decide : ("padding" == "attestation") = false),
      store_get_ne _ _ (by decide : ("data" == "attestation") = false), ha]
  have hd : (encodeAttestationLocals locals a).get? "data" = some (.bytes a.data) := by
    simp only [encodeAttestationLocals, store_get_ne _ _ (by decide : ("padding" == "data") = false), store_get_self]
  have hp : (encodeAttestationLocals locals a).get? "padding" = some (.bytes (ByteArray.zeroes (bytesPadding a.data.size))) := store_get_self _ _ _
  have hh' : (encodeAttestationLocals locals a).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
    simp only [encodeAttestationLocals, store_get_ne _ _ (by decide : ("padding" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("data" == "$EAS.freeMemory") = false), hh]
  change evalExprs? cfg {contract := contract, locals := encodeAttestationLocals locals a, immutables := imms}
    evm [encodeAttestationExpr, .var "$EAS.freeMemory"] = _
  simp only [evalExprs?, encodeAttestation_eval (frame := {contract := contract, locals := encodeAttestationLocals locals a, immutables := imms})
    ha' hd hp hsize, evalExpr?, hh', EvalResult.ofOption, EvalResult.bind, bind, pure]

def encodeAttestationArgs (a : AttestationRecord) (heap : Nat) : Store :=
  ((∅ : Store).insert "$EAS.freeMemory" (.int (Int.ofNat heap))).insert "attestation" a.value

theorem encodeAttestation_lookup : lookupCallable? contract "_encodeAttestation" = some encodeAttestationFunction.toCallable := by rfl

theorem encodeAttestation_bind (a : AttestationRecord) (heap : Nat) :
    bindParams? encodeAttestationFunction.params [a.value, .int (Int.ofNat heap)] = some (encodeAttestationArgs a heap) := by rfl

theorem encodeAttestationCall {cfg : Config} {evm : EVM.State} {locals imms : Store}
    {a : AttestationRecord} {heap : Nat} {args : List Expr} {retVar : Ident}
    (he : evalExprs? cfg {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [a.value, .int (Int.ofNat heap)]) (hsize : a.data.size < UInt256.size) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_encodeAttestation" args retVar)
      (.ok {contract := contract, locals := locals.insert retVar (.tuple [.bytes a.encoding, .int (Int.ofNat heap)]), immutables := imms} evm) := by
  exact internalCallFunctionReturn he encodeAttestation_lookup (encodeAttestation_bind a heap)
    (encodeAttestationSource (store_get_self _ _ _)
      (by simp only [encodeAttestationArgs, store_get_ne _ _ (by decide : ("attestation" == "$EAS.freeMemory") = false), store_get_self]) hsize)

-- LIBRARY CANDIDATE: prepend a normally terminating block to an internal function body.
theorem execFuncBody_append {cfg : Config} {f f' : Frame} {e e' : EVM.State}
    {front suffix : Body} {result : ExecResult}
    (hp : ExecBlock fork cfg f e front (.ok f' e')) (hs : ExecFuncBody fork cfg f' e' suffix result) :
    ExecFuncBody fork cfg f e (front ++ suffix) result := by
  cases hs with
  | execBlockOK h => exact .execBlockOK (execBlock_append hp h)
  | execBlockRet h => exact .execBlockRet (execBlock_append hp h)
  | execBlockRevert h => exact .execBlockRevert (execBlock_append hp h)
  | execBlockBreak h => exact .execBlockBreak (execBlock_append hp h)
  | execBlockContinue h => exact .execBlockContinue (execBlock_append hp h)
  | execBlockStatic h => exact .execBlockStatic (execBlock_append hp h)

def encodeAttestationBodyLocals (locals : Store) (a : AttestationRecord) (heap : Nat) : Store :=
  unpackHeapLocals (locals.insert "body$allocation" (.tuple [.bytes a.encoding, .int (Int.ofNat heap)]))
    "body" "$EAS.freeMemory" (.bytes a.encoding) heap

end Benchmarks.EAS.EAS
