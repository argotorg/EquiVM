import Benchmarks.EAS.EAS.EncodeArraySource
import Benchmarks.EAS.EAS.EncodeValuesSource
import Benchmarks.EAS.EAS.ResolverCallSource
import Reasoning.ExternalCall

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

abbrev resolverManyFunction : FunctionDecl := contract.functions[13]!

def resolverManySelector (revocation : Bool) : List UInt8 :=
  if revocation then [136, 229, 178, 217] else [145, 219, 11, 126]

def resolverManyPayload (ats : List AttestationRecord) (values : List UInt256) (revocation : Bool) : ByteArray :=
  (resolverManySelector revocation).toByteArray ++ (wordBytes [UInt256.ofNat 64, UInt256.ofNat (64+(attestationArrayEncoding ats).size)] ++
    (attestationArrayEncoding ats ++ valuesEncoding values values.length))

def resolverManySelectorExpr : Expr :=
  .ite (.var "revocation") (.fixedBytesLit ⟨3, by decide⟩ [136, 229, 178, 217])
    (.fixedBytesLit ⟨3, by decide⟩ [145, 219, 11, 126])

def resolverManyPayloadExpr : Expr := .abiEncodePacked [
  (.elem (.bytes ⟨3, by decide⟩), .var "selector"), (abiUInt256, .intLit 64),
  (abiUInt256, .binary .add (.intLit 64) (.arrayLength .localVar {base := "body"})),
  (.bytes, .var "body"), (.bytes, .var "valuesBody")]

def resolverManyBodyPrefix : Body := [
  .internalCall "_encodeAttestations" [.var "attestations", .var "$EAS.freeMemory"] "body$allocation",
  .letDecl "body" none (.tupleGet (.var "body$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "body$allocation") 1)]

def resolverManyPrefix : Body := resolverManyBodyPrefix ++ encodeValuesBlock ++ [
  .letDecl "selector" (some (.elem (.bytes ⟨3, by decide⟩))) resolverManySelectorExpr,
  .letDecl "payload" (some .bytes) resolverManyPayloadExpr]

theorem resolverMany_body : resolverManyFunction.body = resolverManyPrefix ++
    [.lowLevelCall (.var "resolver") (.var "value") (.var "payload") "ok" "result", .require (.var "ok")] ++
      resolverResultTail := by native_decide

def resolverManyBodyLocals (locals : Store) (ats : List AttestationRecord) (heap : Nat) : Store :=
  unpackHeapLocals (locals.insert "body$allocation" (.tuple [.bytes (attestationArrayEncoding ats), .int (Int.ofNat heap)]))
    "body" "$EAS.freeMemory" (.bytes (attestationArrayEncoding ats)) heap

theorem resolverManyBodyPrefix_exec {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {heap : Nat}
    (ha : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hdata : ∀ a ∈ ats, a.data.size < UInt256.size)
    (hbound : attestationArrayOffset ats ats.length < UInt256.size) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolverManyBodyPrefix
      (.ok {contract := contract, locals := resolverManyBodyLocals locals ats heap, immutables := imms} evm) := by
  apply ExecBlock.consNormal (encodeAttestationsCall (ats := ats) (heap := heap)
    (by simp only [evalExprs?, evalExpr?, ha, hh, EvalResult.ofOption, EvalResult.bind, bind, pure]) hdata hbound)
  exact unpackHeapResult (store_get_self _ _ _)
    (by simpa only [store_get_ne _ _ (by decide : ("body$allocation" == "$EAS.freeMemory") = false)] using hh)
    (by decide) (by decide)

theorem resolverManyPayload_eval {cfg : Config} {frame : Frame} {evm : EVM.State}
    {ats : List AttestationRecord} {values : List UInt256} {revocation : Bool}
    (hb : frame.locals.get? "body" = some (.bytes (attestationArrayEncoding ats)))
    (hv : frame.locals.get? "valuesBody" = some (.bytes (valuesEncoding values values.length)))
    (hs : frame.locals.get? "selector" = some (.fixedBytes ⟨3, by decide⟩ (resolverManySelector revocation)))
    (hsize : 64+(attestationArrayEncoding ats).size < UInt256.size) :
    evalExpr? cfg frame evm resolverManyPayloadExpr = .ok (.bytes (resolverManyPayload ats values revocation)) := by
  apply evalPackedBytes
  have hselector : encodePackedValue? (.elem (.bytes ⟨3, by decide⟩))
      (.fixedBytes ⟨3, by decide⟩ (resolverManySelector revocation)) = some (resolverManySelector revocation) := by
    cases revocation <;> rfl
  have hoff : evalExpr? cfg frame evm (.binary .add (.intLit 64) (.arrayLength .localVar {base := "body"})) =
      .ok (.int (Int.ofNat (64+(attestationArrayEncoding ats).size))) := by
    simp only [evalExpr?, readLocalPath?, hb, EvalResult.bind, bind, pure,
      evalBinaryOp_add_int_ok, Int.ofNat_eq_natCast, Nat.cast_add]
    rfl
  have hword : encodePackedValue? abiUInt256 (.int (Int.ofNat (64+(attestationArrayEncoding ats).size))) =
      some (EVM.Word.toBytesBE (UInt256.ofNat (64+(attestationArrayEncoding ats).size))) := by
    simpa only [ulit_toNat' _ hsize] using encodePacked_uint256 (UInt256.ofNat (64+(attestationArrayEncoding ats).size))
  have he := evalPackedArgs_cons
    (show evalExpr? cfg frame evm (.var "selector") = .ok (.fixedBytes ⟨3, by decide⟩ (resolverManySelector revocation)) by
      simp only [evalExpr?, hs, EvalResult.ofOption]) hselector
    (evalPackedArgs_cons
      (show evalExpr? cfg frame evm (.intLit 64) = .ok (.int (Int.ofNat (UInt256.ofNat 64).toNat)) by
        simp only [evalExpr?, pure]; rfl) (encodePacked_uint256 (UInt256.ofNat 64))
      (evalPackedArgs_cons hoff hword
        (evalPackedArgs_cons
          (show evalExpr? cfg frame evm (.var "body") = .ok (.bytes (attestationArrayEncoding ats)) by
            simp only [evalExpr?, hb, EvalResult.ofOption]) (encodePacked_dynamic_bytes _)
          (evalPackedArgs_single
            (show evalExpr? cfg frame evm (.var "valuesBody") = .ok (.bytes (valuesEncoding values values.length)) by
              simp only [evalExpr?, hv, EvalResult.ofOption]) (encodePacked_dynamic_bytes _)))))
  simpa only [resolverManyPayload, wordBytes, ByteArray.append_empty, byteArray_toList_eq,
    ByteArray.data_append, Array.toList_append, List.toList_data_toByteArray, toByteArray_eq_toBytesBE,
    List.append_assoc] using he

structure ResolverCallLocals (locals : Store) (resolver : AccountAddress) (value : UInt256) (heap : Nat)
    (payload : ByteArray) : Prop where
  resolver : locals.get? "resolver" = some (.address resolver)
  value : locals.get? "value" = some (.int (Int.ofNat value.toNat))
  heap : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  payload : locals.get? "payload" = some (.bytes payload)

theorem resolverManyPrefix_exec {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {values : List UInt256} {heap : Nat} {revocation : Bool}
    {resolver : AccountAddress} {value : UInt256}
    (ha : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hv : locals.get? "revocation" = some (.bool revocation))
    (hr : locals.get? "resolver" = some (.address resolver))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hvalues : locals.get? "values" = some (.array (values.map fun w => .int (Int.ofNat w.toNat))))
    (hdata : ∀ a ∈ ats, a.data.size < UInt256.size)
    (hbound : attestationArrayOffset ats ats.length < UInt256.size)
    (hvlen : values.length < UInt256.size)
    (hsize : 64+(attestationArrayEncoding ats).size < UInt256.size) :
    ∃ L, ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm resolverManyPrefix
      (.ok {contract := contract, locals := L, immutables := imms} evm) ∧
      ResolverCallLocals L resolver value heap (resolverManyPayload ats values revocation) := by
  have hb := resolverManyBodyPrefix_exec (fork := fork) (cfg := cfg) (imms := imms) (evm := evm) ha hh hdata hbound
  have hvs : (resolverManyBodyLocals locals ats heap).get? "values" = some (.array (values.map fun w => .int (Int.ofNat w.toNat))) := by
    simp (disch := decide) only [resolverManyBodyLocals, unpackHeapLocals, store_get_ne, hvalues]
  obtain ⟨L, hl, hinv⟩ := encodeValuesBlock_exec (cfg := cfg) (imms := imms) (evm := evm) hvs hvlen
  have hp (key : Ident) (hkey : ("valuesBody" == key) = false) (hki : ("i" == key) = false) := hinv.preserved key hkey hki
  have hbody : L.get? "body" = some (.bytes (attestationArrayEncoding ats)) := by
    rw [hp "body" (by decide) (by decide)]
    simp (disch := decide) only [resolverManyBodyLocals, unpackHeapLocals, store_get_ne, store_get_self]
  have hrev : L.get? "revocation" = some (.bool revocation) := by
    rw [hp "revocation" (by decide) (by decide)]
    simp (disch := decide) only [resolverManyBodyLocals, unpackHeapLocals, store_get_ne, hv]
  let L1 := L.insert "selector" (.fixedBytes ⟨3, by decide⟩ (resolverManySelector revocation))
  let L2 := L1.insert "payload" (.bytes (resolverManyPayload ats values revocation))
  refine ⟨L2, ?_, ?_⟩
  · unfold resolverManyPrefix
    rw [List.append_assoc]
    apply execBlock_append hb
    apply execBlock_append hl
    apply ExecBlock.consNormal (ExecStmt.letDecl (value := .fixedBytes ⟨3, by decide⟩ (resolverManySelector revocation)) (by
      change evalExpr? cfg {contract := contract, locals := L, immutables := imms} evm resolverManySelectorExpr = _
      simp only [resolverManySelectorExpr, evalExpr?, hrev, EvalResult.ofOption, EvalResult.bind, bind]
      cases revocation <;> rfl))
    apply ExecBlock.consNormal (ExecStmt.letDecl (resolverManyPayload_eval ?_ ?_ (store_get_self _ _ _) hsize)) ExecBlock.nil
    · simpa (disch := decide) only [store_get_ne] using hbody
    · simpa (disch := decide) only [store_get_ne] using hinv.encoded
  · constructor
    · simp (disch := decide) only [L2, L1, store_get_ne, hp "resolver" (by decide) (by decide),
        resolverManyBodyLocals, unpackHeapLocals, hr]
    · simp (disch := decide) only [L2, L1, store_get_ne, hp "value" (by decide) (by decide),
        resolverManyBodyLocals, unpackHeapLocals, hvalue]
    · simp (disch := decide) only [L2, L1, store_get_ne, hp "$EAS.freeMemory" (by decide) (by decide),
        resolverManyBodyLocals, unpackHeapLocals, store_get_self]
    · exact store_get_self _ _ _



theorem resolverManySource {locals imms : Store} {evm evm' : EVM.State}
    {ats : List AttestationRecord} {values : List UInt256} {heap : Nat} {revocation success : Bool}
    {resolver : AccountAddress} {value : UInt256} {out : ByteArray}
    (ha : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hv : locals.get? "revocation" = some (.bool revocation))
    (hr : locals.get? "resolver" = some (.address resolver))
    (hvalue : locals.get? "value" = some (.int (Int.ofNat value.toNat)))
    (hvalues : locals.get? "values" = some (.array (values.map fun w => .int (Int.ofNat w.toNat))))
    (hdata : ∀ a ∈ ats, a.data.size < UInt256.size)
    (hbound : attestationArrayOffset ats ats.length < UInt256.size)
    (hvlen : values.length < UInt256.size)
    (hsize : 64+(attestationArrayEncoding ats).size < UInt256.size)
    (hc : callViaEVM fork evm resolver (Int.ofNat value.toNat) (resolverManyPayload ats values revocation) (success, evm', out))
    (hout : out.size < 2^255)
    (hperm : EVM.wordOfInt (Int.ofNat value.toNat) = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    if resolverCallValid heap success out then
      ∃ L, ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm resolverManyFunction.body
        (.returned {contract := contract, locals := L, immutables := imms} evm'
          (some [.bool (decide (calldataWord out 0 ≠ ⟨0⟩)), .int (Int.ofNat (allocateNext heap (min out.size 32)))]))
    else ExecFuncBody fork config {contract := contract, locals := locals, immutables := imms} evm resolverManyFunction.body .reverted := by
  obtain ⟨L, hp, hf⟩ := resolverManyPrefix_exec (cfg := config) (imms := imms) (evm := evm)
    ha hh hv hr hvalue hvalues hdata hbound hvlen hsize
  let L' := (L.insert "ok" (.bool success)).insert "result" (.bytes out)
  have hcall : ExecBlock fork config {contract := contract, locals := L, immutables := imms} evm
      [.lowLevelCall (.var "resolver") (.var "value") (.var "payload") "ok" "result"]
      (.ok {contract := contract, locals := L', immutables := imms} evm') := by
    exact ExecBlock.consNormal (lowLevelCallSource (fork := fork) (hperm := hperm)
      (by simp only [evalExpr?, hf.resolver, EvalResult.ofOption])
      (by simp only [evalExpr?, hf.value, EvalResult.ofOption])
      (by simp only [evalExpr?, hf.payload, EvalResult.ofOption]) hc) ExecBlock.nil
  have hok : L'.get? "ok" = some (.bool success) := by
    simp (disch := decide) only [L', store_get_ne, store_get_self]
  have hho : L'.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) := by
    simp (disch := decide) only [L', store_get_ne, hf.heap]
  have hs := resolverCallResultSource (fork := fork) (imms := imms) (evm := evm') hok (store_get_self _ _ _) hho hout
  have hbody : resolverManyFunction.body = (resolverManyPrefix ++
      [.lowLevelCall (.var "resolver") (.var "value") (.var "payload") "ok" "result"]) ++
      (.require (.var "ok") :: resolverResultTail) := by
    rw [resolverMany_body, List.append_assoc, List.append_assoc]
    rfl
  by_cases hg : resolverCallValid heap success out
  · rw [if_pos hg, hbody]
    rw [if_pos hg] at hs
    exact ⟨resolverResultFinalLocals L' out heap, execFuncBody_append (execBlock_append hp hcall) hs⟩
  · rw [if_neg hg, hbody]
    rw [if_neg hg] at hs
    exact execFuncBody_append (execBlock_append hp hcall) hs

def resolverManyArgs (resolver : AccountAddress) (ats : List AttestationRecord) (values : List UInt256)
    (revocation : Bool) (value : UInt256) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap))
    |>.insert "value" (.int (Int.ofNat value.toNat)) |>.insert "revocation" (.bool revocation)
    |>.insert "values" (.array (values.map fun w => .int (Int.ofNat w.toNat)))
    |>.insert "attestations" (.array (ats.map AttestationRecord.value)) |>.insert "resolver" (.address resolver)

theorem resolverManyArgs_facts (resolver : AccountAddress) (ats : List AttestationRecord) (values : List UInt256)
    (revocation : Bool) (value : UInt256) (heap : Nat) :
    (resolverManyArgs resolver ats values revocation value heap).get? "attestations" = some (.array (ats.map AttestationRecord.value)) ∧
    (resolverManyArgs resolver ats values revocation value heap).get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)) ∧
    (resolverManyArgs resolver ats values revocation value heap).get? "revocation" = some (.bool revocation) ∧
    (resolverManyArgs resolver ats values revocation value heap).get? "resolver" = some (.address resolver) ∧
    (resolverManyArgs resolver ats values revocation value heap).get? "value" = some (.int (Int.ofNat value.toNat)) ∧
    (resolverManyArgs resolver ats values revocation value heap).get? "values" = some (.array (values.map fun w => .int (Int.ofNat w.toNat))) := by
  simp (disch := decide) only [resolverManyArgs, store_get_ne, store_get_self, and_self]

theorem resolverMany_lookup : lookupCallable? contract "_resolverMany" = some resolverManyFunction.toCallable := by rfl

theorem resolverMany_bind (resolver : AccountAddress) (ats : List AttestationRecord) (values : List UInt256)
    (revocation : Bool) (value : UInt256) (heap : Nat) :
    bindParams? resolverManyFunction.params [.address resolver, .array (ats.map AttestationRecord.value),
      .array (values.map fun w => .int (Int.ofNat w.toNat)), .bool revocation, .int (Int.ofNat value.toNat), .int (Int.ofNat heap)] =
      some (resolverManyArgs resolver ats values revocation value heap) := by rfl

theorem resolverManyCall {locals imms : Store} {evm evm' : EVM.State}
    {ats : List AttestationRecord} {values : List UInt256} {heap : Nat} {revocation success : Bool}
    {resolver : AccountAddress} {value : UInt256} {out : ByteArray} {args : List Expr} {retVar : Ident}
    (he : evalExprs? config {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.address resolver, .array (ats.map AttestationRecord.value),
        .array (values.map fun w => .int (Int.ofNat w.toNat)), .bool revocation, .int (Int.ofNat value.toNat), .int (Int.ofNat heap)])
    (hdata : ∀ a ∈ ats, a.data.size < UInt256.size)
    (hbound : attestationArrayOffset ats ats.length < UInt256.size)
    (hvlen : values.length < UInt256.size)
    (hsize : 64+(attestationArrayEncoding ats).size < UInt256.size)
    (hc : callViaEVM fork evm resolver (Int.ofNat value.toNat) (resolverManyPayload ats values revocation) (success, evm', out))
    (hout : out.size < 2^255)
    (hperm : EVM.wordOfInt (Int.ofNat value.toNat) = ⟨0⟩ ∨ evm.executionEnv.perm = true) :
    if resolverCallValid heap success out then
      ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
        (.internalCall "_resolverMany" args retVar)
        (.ok {contract := contract, locals := locals.insert retVar (.tuple [
          .bool (decide (calldataWord out 0 ≠ ⟨0⟩)), .int (Int.ofNat (allocateNext heap (min out.size 32)))]), immutables := imms} evm')
    else ExecStmt fork config {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_resolverMany" args retVar) .reverted := by
  have hf := resolverManyArgs_facts resolver ats values revocation value heap
  have hs := resolverManySource (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (imms := imms) hf.1 hf.2.1 hf.2.2.1 hf.2.2.2.1 hf.2.2.2.2.1 hf.2.2.2.2.2
    hdata hbound hvlen hsize hc hout
  by_cases hg : resolverCallValid heap success out
  · rw [if_pos hg] at hs ⊢
    obtain ⟨L, hs⟩ := hs
    exact internalCallFunctionReturn he resolverMany_lookup (resolverMany_bind resolver ats values revocation value heap) hs
  · rw [if_neg hg] at hs ⊢
    exact internalCallFunctionRevert he resolverMany_lookup (resolverMany_bind resolver ats values revocation value heap) hs

end Benchmarks.EAS.EAS
