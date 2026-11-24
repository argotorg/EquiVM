import Benchmarks.EAS.EAS.RecordEncoding
import Benchmarks.EAS.EAS.ResolverCallSource
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

def resolverOneSelector (revocation : Bool) : List UInt8 :=
  if revocation then [228, 150, 23, 225] else [230, 12, 53, 5]

def resolverOnePayload (a : AttestationRecord) (revocation : Bool) : ByteArray :=
  (resolverOneSelector revocation).toByteArray ++ ((UInt256.ofNat 32).toByteArray ++ a.encoding)

def resolverOneSelectorExpr : Expr :=
  .ite (.var "revocation") (.fixedBytesLit ⟨3, by decide⟩ [228, 150, 23, 225])
    (.fixedBytesLit ⟨3, by decide⟩ [230, 12, 53, 5])

def resolverOnePayloadExpr : Expr := .abiEncodePacked [
  (.elem (.bytes ⟨3, by decide⟩), .var "selector"), (abiUInt256, .intLit 32), (.bytes, .var "body")]

def resolverOnePrefix : Body := [
  .internalCall "_encodeAttestation" [.var "attestation", .var "$EAS.freeMemory"] "body$allocation",
  .letDecl "body" none (.tupleGet (.var "body$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "body$allocation") 1),
  .letDecl "selector" (some (.elem (.bytes ⟨3, by decide⟩))) resolverOneSelectorExpr,
  .letDecl "payload" (some .bytes) resolverOnePayloadExpr]

abbrev resolverOneFunction : FunctionDecl := contract.functions[12]!

theorem resolverOne_body : resolverOneFunction.body = resolverOnePrefix ++
    [.lowLevelCall (.var "resolver") (.var "value") (.var "payload") "ok" "result", .require (.var "ok")] ++
      resolverResultTail := by native_decide

theorem resolverOnePayload_eval {cfg : Config} {frame : Frame} {evm : EVM.State}
    {a : AttestationRecord} {revocation : Bool}
    (hb : frame.locals.get? "body" = some (.bytes a.encoding))
    (hs : frame.locals.get? "selector" = some (.fixedBytes ⟨3, by decide⟩ (resolverOneSelector revocation))) :
    evalExpr? cfg frame evm resolverOnePayloadExpr = .ok (.bytes (resolverOnePayload a revocation)) := by
  have he : encodePackedValue? (.elem (.bytes ⟨3, by decide⟩))
      (.fixedBytes ⟨3, by decide⟩ (resolverOneSelector revocation)) = some (resolverOneSelector revocation) := by
    cases revocation <;> rfl
  have hp : evalPackedArgs? cfg frame evm [
      (.elem (.bytes ⟨3, by decide⟩), .var "selector"), (abiUInt256, .intLit 32), (.bytes, .var "body")] =
      .ok (resolverOneSelector revocation ++ (EVM.Word.toBytesBE (UInt256.ofNat 32) ++ a.encoding.toList)) := by
    apply evalPackedArgs_cons (by simp only [evalExpr?, hs, EvalResult.ofOption]) he
    apply evalPackedArgs_cons (by simp only [evalExpr?, pure]; rfl) (encodePacked_uint256 (UInt256.ofNat 32))
    exact evalPackedArgs_single (by simp only [evalExpr?, hb, EvalResult.ofOption]) (encodePacked_dynamic_bytes _)
  simp only [resolverOnePayloadExpr, evalExpr?, hp, EvalResult.bind, bind, pure]
  apply congrArg (fun b => EvalResult.ok (Value.bytes b))
  apply byteArray_eq_of_toList_eq
  simp only [resolverOnePayload, byteArray_toList_eq, ByteArray.data_append, Array.toList_append,
    List.toList_toArray, toByteArray_eq_toBytesBE, List.toList_data_toByteArray]

def resolverOnePrefixLocals (locals : Store) (a : AttestationRecord) (heap : Nat) (revocation : Bool) : Store :=
  ((encodeAttestationBodyLocals locals a heap).insert "selector" (.fixedBytes ⟨3, by decide⟩ (resolverOneSelector revocation))).insert
    "payload" (.bytes (resolverOnePayload a revocation))

theorem resolverOnePrefix_exec {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {a : AttestationRecord} {heap : Nat} {revocation : Bool}
    (ha : locals.get? "attestation" = some a.value)
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hv : locals.get? "revocation" = some (.bool revocation)) (hsize : a.data.size < UInt256.size) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolverOnePrefix
      (.ok {contract := contract, locals := resolverOnePrefixLocals locals a heap revocation, immutables := imms} evm) := by
  apply ExecBlock.consNormal (encodeAttestationCall (a := a) (heap := heap)
    (by simp only [evalExprs?, evalExpr?, ha, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]) hsize)
  apply execBlock_append (s1 := [
    .letDecl "body" none (.tupleGet (.var "body$allocation") 0),
    .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "body$allocation") 1)])
    (unpackHeapResult (store_get_self _ _ _)
      (by simpa only [store_get_ne _ _ (by decide : ("body$allocation" == "$EAS.freeMemory") = false)] using hh)
      (by decide) (by decide))
  have hv' : (encodeAttestationBodyLocals locals a heap).get? "revocation" = some (.bool revocation) := by
    simpa only [encodeAttestationBodyLocals, unpackHeapLocals,
      store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "revocation") = false),
      store_get_ne _ _ (by decide : ("body" == "revocation") = false),
      store_get_ne _ _ (by decide : ("body$allocation" == "revocation") = false)] using hv
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .fixedBytes ⟨3, by decide⟩ (resolverOneSelector revocation)) (by
    change evalExpr? cfg {contract := contract, locals := encodeAttestationBodyLocals locals a heap, immutables := imms} evm resolverOneSelectorExpr = _
    simp only [resolverOneSelectorExpr, evalExpr?, hv', EvalResult.ofOption, EvalResult.bind, bind]
    cases revocation <;> rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (resolverOnePayload_eval ?_ (store_get_self _ _ _))) ExecBlock.nil
  simp only [encodeAttestationBodyLocals, unpackHeapLocals,
    store_get_ne _ _ (by decide : ("selector" == "body") = false),
    store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "body") = false), store_get_self]

theorem resolverOnePrefixLocals_facts (locals : Store) (a : AttestationRecord) (heap : Nat) (revocation : Bool) :
    (resolverOnePrefixLocals locals a heap revocation).get? "resolver" = locals.get? "resolver" ∧
    (resolverOnePrefixLocals locals a heap revocation).get? "value" = locals.get? "value" ∧
    (resolverOnePrefixLocals locals a heap revocation).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) ∧
    (resolverOnePrefixLocals locals a heap revocation).get? "payload" = some (.bytes (resolverOnePayload a revocation)) := by
  simp (disch := decide) only [resolverOnePrefixLocals, encodeAttestationBodyLocals, unpackHeapLocals,
    store_get_ne, store_get_self, and_self]

def resolverOnePostLocals (locals : Store) (a : AttestationRecord) (heap : Nat) (revocation success : Bool)
    (out : ByteArray) : Store :=
  ((resolverOnePrefixLocals locals a heap revocation).insert "ok" (.bool success)).insert "result" (.bytes out)

def resolverOnePreamble : Body := resolverOnePrefix ++
  [.lowLevelCall (.var "resolver") (.var "value") (.var "payload") "ok" "result"]

theorem resolverOnePreamble_exec {cfg : Config} {locals imms : Store} {evm evm' : EVM.State}
    {a : AttestationRecord} {heap : Nat} {revocation success : Bool} {out : ByteArray}
    {resolver : AccountAddress} {value : UInt256}
    (ha : locals.get? "attestation" = some a.value)
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hv : locals.get? "revocation" = some (.bool revocation))
    (hr : locals.get? "resolver" = some (.address resolver))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hsize : a.data.size < UInt256.size)
    (hc : callViaEVM fork evm resolver (Int.ofNat value.toNat) (resolverOnePayload a revocation) (success, evm', out))
    (hperm : EVM.wordOfInt (Int.ofNat value.toNat) = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolverOnePreamble
      (.ok {contract := contract, locals := resolverOnePostLocals locals a heap revocation success out, immutables := imms} evm') := by
  apply execBlock_append (resolverOnePrefix_exec ha hh hv hsize)
  have hf := resolverOnePrefixLocals_facts locals a heap revocation
  exact ExecBlock.consNormal (lowLevelCallSource (fork := fork) (hperm := hperm)
    (by simp only [evalExpr?, hf.1, hr, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.2.1, hvalue, EvalResult.ofOption])
    (by simp only [evalExpr?, hf.2.2.2, EvalResult.ofOption]) hc) ExecBlock.nil

def resolverOneFinalLocals (locals : Store) (a : AttestationRecord) (heap : Nat) (revocation success : Bool)
    (out : ByteArray) : Store :=
  resolverResultFinalLocals (resolverOnePostLocals locals a heap revocation success out) out heap

theorem resolverOneSource {locals imms : Store} {evm evm' : EVM.State}
    {a : AttestationRecord} {heap : Nat} {revocation success : Bool} {out : ByteArray}
    {resolver : AccountAddress} {value : UInt256}
    (ha : locals.get? "attestation" = some a.value)
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hv : locals.get? "revocation" = some (.bool revocation))
    (hr : locals.get? "resolver" = some (.address resolver))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hsize : a.data.size < UInt256.size)
    (hc : callViaEVM fork evm resolver (Int.ofNat value.toNat) (resolverOnePayload a revocation) (success, evm', out))
    (hout : out.size < 2^255)
    (hperm : EVM.wordOfInt (Int.ofNat value.toNat) = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    if resolverCallValid heap success out then
      ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm resolverOneFunction.body
        (.returned {contract := contract, locals := resolverOneFinalLocals locals a heap revocation success out, immutables := imms}
          evm' (some [.bool (decide (calldataWord out 0 ≠ ⟨0⟩)), .int (Int.ofNat (allocateNext heap (min out.size 32)))]))
    else ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm resolverOneFunction.body .reverted := by
  have hp := resolverOnePreamble_exec (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (cfg := config) (imms := imms) ha hh hv hr hvalue hsize hc
  have hbody : resolverOneFunction.body = resolverOnePreamble ++ (.require (.var "ok") :: resolverResultTail) := by
    rw [resolverOne_body, resolverOnePreamble, List.append_assoc]
    rfl
  have hho : (resolverOnePostLocals locals a heap revocation success out).get? "$EAS.freeMemory" =
      some (.int (Int.ofNat heap)) := by
    simp only [resolverOnePostLocals,
      store_get_ne _ _ (by decide : ("result" == "$EAS.freeMemory") = false),
      store_get_ne _ _ (by decide : ("ok" == "$EAS.freeMemory") = false),
      (resolverOnePrefixLocals_facts locals a heap revocation).2.2.1]
  have hok : (resolverOnePostLocals locals a heap revocation success out).get? "ok" = some (.bool success) := by
    simp only [resolverOnePostLocals, store_get_ne _ _ (by decide : ("result" == "ok") = false), store_get_self]
  have hor : (resolverOnePostLocals locals a heap revocation success out).get? "result" = some (.bytes out) := store_get_self _ _ _
  have hs := resolverCallResultSource (fork := fork) (imms := imms) (evm := evm') hok hor hho hout
  by_cases hvalid : resolverCallValid heap success out
  · rw [if_pos hvalid, hbody]
    rw [if_pos hvalid] at hs
    exact execFuncBody_append hp hs
  · rw [if_neg hvalid, hbody]
    rw [if_neg hvalid] at hs
    exact execFuncBody_append hp hs

def resolverOneArgs (resolver : AccountAddress) (a : AttestationRecord) (revocation : Bool) (value : UInt256)
    (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap))
    |>.insert "value" (.int (Int.ofNat value.toNat)) |>.insert "revocation" (.bool revocation)
    |>.insert "attestation" a.value |>.insert "resolver" (.address resolver)

theorem resolverOneArgs_facts (resolver : AccountAddress) (a : AttestationRecord) (revocation : Bool) (value : UInt256)
    (heap : Nat) :
    (resolverOneArgs resolver a revocation value heap).get? "attestation" = some a.value ∧
    (resolverOneArgs resolver a revocation value heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) ∧
    (resolverOneArgs resolver a revocation value heap).get? "revocation" = some (.bool revocation) ∧
    (resolverOneArgs resolver a revocation value heap).get? "resolver" = some (.address resolver) ∧
    (resolverOneArgs resolver a revocation value heap).get? "value" = some (.int (Int.ofNat value.toNat)) := by
  simp (disch := decide) only [resolverOneArgs, store_get_ne, store_get_self, and_self]

theorem resolverOne_lookup : lookupCallable? contract "_resolverOne" = some resolverOneFunction.toCallable := by rfl

theorem resolverOne_bind (resolver : AccountAddress) (a : AttestationRecord) (revocation : Bool) (value : UInt256)
    (heap : Nat) :
    bindParams? resolverOneFunction.params [.address resolver, a.value, .bool revocation,
      .int (Int.ofNat value.toNat), .int (Int.ofNat heap)] = some (resolverOneArgs resolver a revocation value heap) := by rfl

theorem resolverOneCall {locals imms : Store} {evm evm' : EVM.State}
    {a : AttestationRecord} {heap : Nat} {revocation success : Bool} {out : ByteArray}
    {resolver : AccountAddress} {value : UInt256} {args : List Expr} {retVar : Ident}
    (he : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.address resolver, a.value, .bool revocation, .int (Int.ofNat value.toNat), .int (Int.ofNat heap)])
    (hsize : a.data.size < UInt256.size)
    (hc : callViaEVM fork evm resolver (Int.ofNat value.toNat) (resolverOnePayload a revocation) (success, evm', out))
    (hout : out.size < 2^255)
    (hperm : EVM.wordOfInt (Int.ofNat value.toNat) = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    if resolverCallValid heap success out then
      ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
        (.internalCall "_resolverOne" args retVar)
        (.ok {contract := contract, locals := locals.insert retVar (.tuple [
          .bool (decide (calldataWord out 0 ≠ ⟨0⟩)), .int (Int.ofNat (allocateNext heap (min out.size 32)))]), immutables := imms} evm')
    else ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_resolverOne" args retVar) .reverted := by
  have hf := resolverOneArgs_facts resolver a revocation value heap
  have hs := resolverOneSource (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (imms := imms) hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2 hsize hc hout
  by_cases hv : resolverCallValid heap success out
  · rw [if_pos hv] at hs ⊢
    exact internalCallFunctionReturn he resolverOne_lookup (resolverOne_bind resolver a revocation value heap) hs
  · rw [if_neg hv] at hs ⊢
    exact internalCallFunctionRevert he resolverOne_lookup (resolverOne_bind resolver a revocation value heap) hs

end Benchmarks.EAS.EAS
