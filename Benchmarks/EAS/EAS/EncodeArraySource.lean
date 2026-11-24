import Benchmarks.EAS.EAS.ArrayEncoding

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000
set_option maxHeartbeats 200000

abbrev encodeAttestationsFunction : FunctionDecl := contract.functions[11]!

def encodeArrayInit : Body := [
  .letDecl "heads" (some .bytes) (.newBytes (.intLit 0)),
  .letDecl "tails" (some .bytes) (.newBytes (.intLit 0)),
  .letDecl "offset" (some abiUInt256) (.binary .mul (.arrayLength .localVar {base := "attestations"}) (.intLit 32)),
  .letDecl "i" (some abiUInt256) (.intLit 0)]

def encodeArrayGuard : Expr := .binary .lt (.var "i") (.arrayLength .localVar {base := "attestations"})

def encodeArrayIteration : Body := [
  .internalCall "_encodeAttestation" [.index (.var "attestations") (.var "i"), .var "$EAS.freeMemory"] "body$allocation",
  .letDecl "body" none (.tupleGet (.var "body$allocation") 0),
  .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "body$allocation") 1),
  .assign .localVar {base := "heads"} (.abiEncodePacked [(.bytes, .var "heads"), (abiUInt256, .var "offset")]),
  .assign .localVar {base := "tails"} (.abiEncodePacked [(.bytes, .var "tails"), (.bytes, .var "body")]),
  .assign .localVar {base := "offset"} (.binary .add (.var "offset") (.arrayLength .localVar {base := "body"})),
  .assign .localVar {base := "i"} (.binary .add (.var "i") (.intLit 1))]

def encodeArrayResult : Expr := .abiEncodePacked [
  (abiUInt256, .arrayLength .localVar {base := "attestations"}), (.bytes, .var "heads"), (.bytes, .var "tails")]

theorem encodeAttestations_body : encodeAttestationsFunction.body = encodeArrayInit ++
    [.while encodeArrayGuard encodeArrayIteration, .return [encodeArrayResult, .var "$EAS.freeMemory"],
      .return [.tupleLit [], .var "$EAS.freeMemory"]] := by native_decide

structure EncodeArrayInv (locals : Store) (ats : List AttestationRecord) (heap i : Nat) : Prop where
  attestations : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value))
  heap : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))
  heads : locals.get? "heads" = some (.bytes (wordBytes (attestationArrayHeads ats i)))
  tails : locals.get? "tails" = some (.bytes (attestationArrayBodies ats i))
  offset : locals.get? "offset" = some (.int (Int.ofNat (attestationArrayOffset ats i)))
  index : locals.get? "i" = some (.int (Int.ofNat i))

def encodeArrayInitLocals (locals : Store) (ats : List AttestationRecord) : Store :=
  locals |>.insert "heads" (.bytes .empty) |>.insert "tails" (.bytes .empty)
    |>.insert "offset" (.int (Int.ofNat (32*ats.length))) |>.insert "i" (.int 0)

theorem encodeArrayInit_exec {cfg : Config} {locals imms : Store} {evm : EVM.State} {ats : List AttestationRecord}
    (ha : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value))) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm encodeArrayInit
      (.ok {contract := contract, locals := encodeArrayInitLocals locals ats, immutables := imms} evm) := by
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes .empty) (by simp [evalExpr?, EvalResult.bind, bind, pure, ByteArray.empty, ByteArray.emptyWithCapacity] <;> rfl))
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes .empty) (by simp [evalExpr?, EvalResult.bind, bind, pure, ByteArray.empty, ByteArray.emptyWithCapacity] <;> rfl))
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .int (Int.ofNat (32*ats.length))) ?_) ?_
  · simp only [evalExpr?, readLocalPath?,
      store_get_ne _ _ (by decide : ("tails" == "attestations") = false),
      store_get_ne _ _ (by decide : ("heads" == "attestations") = false), ha,
      EvalResult.bind, bind, pure, List.length_map, evalBinaryOp?, Int.ofNat_eq_natCast, Nat.cast_mul]
    congr 2
    omega
  exact ExecBlock.consNormal (ExecStmt.letDecl (value := .int 0) (by simp only [evalExpr?, pure])) ExecBlock.nil

theorem encodeArrayInit_inv {locals : Store} {ats : List AttestationRecord} {heap : Nat}
    (ha : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap))) :
    EncodeArrayInv (encodeArrayInitLocals locals ats) ats heap 0 := by
  constructor <;> simp (disch := decide) only [encodeArrayInitLocals, store_get_ne, store_get_self,
    attestationArrayHeads, attestationArrayBodies, attestationArrayOffset, List.take_zero, List.map_nil,
    dynamicOffsets, dynamicBodies, wordBytes, ByteArray.size_empty, Nat.add_zero, ha, hh] <;> rfl

theorem encodeArrayGuard_eval {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {heap i : Nat} (h : EncodeArrayInv locals ats heap i) :
    evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm encodeArrayGuard =
      .ok (.bool (decide (i < ats.length))) := by
  simp only [encodeArrayGuard, evalExpr?, h.index, readLocalPath?, h.attestations,
    List.length_map, EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp_lt_int_ok,
    Int.ofNat_eq_natCast, Nat.cast_lt]

theorem encodeArrayArgs_eval {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {heap i : Nat} (h : EncodeArrayInv locals ats heap i) (hi : i < ats.length) :
    evalExprs? cfg {contract := contract, locals := locals, immutables := imms} evm
      [.index (.var "attestations") (.var "i"), .var "$EAS.freeMemory"] =
      .ok [ats[i].value, .int (Int.ofNat heap)] := by
  have hw : lookupNth? ats i = some ats[i] := (lookupNth_getElem ats i).trans (List.getElem?_eq_getElem hi)
  simp only [evalExprs?, evalExpr?, h.attestations, h.index, h.heap,
    EvalResult.ofOption, EvalResult.bind, bind, evalIndex?, Int.ofNat_eq_natCast,
    Int.natCast_nonneg, List.length_map, Nat.cast_lt, hi, and_self, if_true,
    Int.toNat_natCast, lookupNth_map, hw,
    Option.map_some, AttestationRecord.value, normalizeRawBoolWord?, pure]



def encodeArrayNext (locals : Store) (ats : List AttestationRecord) (heap i : Nat) (a : AttestationRecord) : Store :=
  encodeAttestationBodyLocals locals a heap
    |>.insert "heads" (.bytes (wordBytes (attestationArrayHeads ats i ++ [UInt256.ofNat (attestationArrayOffset ats i)])))
    |>.insert "tails" (.bytes (attestationArrayBodies ats i ++ a.encoding))
    |>.insert "offset" (.int (Int.ofNat (attestationArrayOffset ats i+a.encoding.size)))
    |>.insert "i" (.int (Int.ofNat (i+1)))

theorem encodeArrayBody_inv {locals : Store} {ats : List AttestationRecord} {heap i : Nat}
    (h : EncodeArrayInv locals ats heap i) (a : AttestationRecord) :
    EncodeArrayInv (encodeAttestationBodyLocals locals a heap) ats heap i := by
  constructor <;> simp (disch := decide) only [encodeAttestationBodyLocals, unpackHeapLocals,
    store_get_ne, store_get_self, h.attestations, h.heap, h.heads, h.tails, h.offset, h.index]

theorem encodeArrayNext_inv {locals : Store} {ats : List AttestationRecord} {heap i : Nat}
    (h : EncodeArrayInv locals ats heap i) (hi : i < ats.length) :
    EncodeArrayInv (encodeArrayNext locals ats heap i ats[i]) ats heap (i+1) := by
  have hs := attestationArray_step ats i hi
  have hb := encodeArrayBody_inv h ats[i]
  constructor <;> simp (disch := decide) only [encodeArrayNext, store_get_ne, store_get_self,
    hb.attestations, hb.heap, hs.1, hs.2.1, hs.2.2]

theorem encodeArrayIteration_exec {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {heap i : Nat} (h : EncodeArrayInv locals ats heap i)
    (hi : i < ats.length) (hdata : ats[i].data.size < UInt256.size)
    (hoff : attestationArrayOffset ats i < UInt256.size) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm encodeArrayIteration
      (.ok {contract := contract, locals := encodeArrayNext locals ats heap i ats[i], immutables := imms} evm) := by
  apply ExecBlock.consNormal (encodeAttestationCall (encodeArrayArgs_eval h hi) hdata)
  apply execBlock_append (s1 := [
    .letDecl "body" none (.tupleGet (.var "body$allocation") 0),
    .assign .localVar {base := "$EAS.freeMemory"} (.tupleGet (.var "body$allocation") 1)])
    (unpackHeapResult (store_get_self _ _ _)
      (by simpa only [store_get_ne _ _ (by decide : ("body$allocation" == "$EAS.freeMemory") = false)] using h.heap)
      (by decide) (by decide))
  let base := encodeAttestationBodyLocals locals ats[i] heap
  have hb : EncodeArrayInv base ats heap i := encodeArrayBody_inv h _
  have hbody : base.get? "body" = some (.bytes ats[i].encoding) := by
    simp only [base, encodeAttestationBodyLocals, unpackHeapLocals,
      store_get_ne _ _ (by decide : ("$EAS.freeMemory" == "body") = false), store_get_self]
  let L1 := base.insert "heads" (.bytes (wordBytes (attestationArrayHeads ats i ++ [UInt256.ofNat (attestationArrayOffset ats i)])))
  let L2 := L1.insert "tails" (.bytes (attestationArrayBodies ats i ++ ats[i].encoding))
  let L3 := L2.insert "offset" (.int (Int.ofNat (attestationArrayOffset ats i+ats[i].encoding.size)))
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›)
    (value := .bytes (wordBytes (attestationArrayHeads ats i ++ [UInt256.ofNat (attestationArrayOffset ats i)]))) ?_
    (assignLocalBase_ok (frame := {contract := contract, locals := base, immutables := imms}) hb.heads)) ?_
  · apply evalPackedBytes
    rw [wordBytes_append]
    change evalPackedArgs? cfg {contract := contract, locals := base, immutables := imms} evm _ = _
    have he := evalPackedArgs_cons
      (show evalExpr? cfg {contract := contract, locals := base, immutables := imms} evm (.var "heads") =
        .ok (.bytes (wordBytes (attestationArrayHeads ats i))) by simp only [evalExpr?, hb.heads, EvalResult.ofOption])
      (encodePacked_dynamic_bytes _)
      (evalPackedArgs_single
        (show evalExpr? cfg {contract := contract, locals := base, immutables := imms} evm (.var "offset") =
          .ok (.int (Int.ofNat (attestationArrayOffset ats i))) by simp only [evalExpr?, hb.offset, EvalResult.ofOption])
        (by simpa only [ulit_toNat' _ hoff] using encodePacked_uint256 (UInt256.ofNat (attestationArrayOffset ats i))))
    simpa only [wordBytes, ByteArray.append_empty, byteArray_toList_eq, ByteArray.data_append,
      Array.toList_append, toByteArray_eq_toBytesBE] using he
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›)
    (value := .bytes (attestationArrayBodies ats i ++ ats[i].encoding)) ?_
    (assignLocalBase_ok (frame := {contract := contract, locals := L1, immutables := imms})
      (by simpa (disch := decide) only [L1, store_get_ne] using hb.tails))) ?_
  · apply evalPackedBytes
    have he := evalPackedArgs_cons
      (show evalExpr? cfg {contract := contract, locals := L1, immutables := imms} evm (.var "tails") =
        .ok (.bytes (attestationArrayBodies ats i)) by
          simp (disch := decide) only [evalExpr?, L1, store_get_ne, hb.tails, EvalResult.ofOption])
      (encodePacked_dynamic_bytes _)
      (evalPackedArgs_single
        (show evalExpr? cfg {contract := contract, locals := L1, immutables := imms} evm (.var "body") =
          .ok (.bytes ats[i].encoding) by
            simp (disch := decide) only [evalExpr?, L1, store_get_ne, hbody, EvalResult.ofOption])
        (encodePacked_dynamic_bytes _))
    simpa only [byteArray_toList_eq, ByteArray.data_append, Array.toList_append] using he
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›)
    (value := .int (Int.ofNat (attestationArrayOffset ats i+ats[i].encoding.size))) ?_
    (assignLocalBase_ok (frame := {contract := contract, locals := L2, immutables := imms})
      (by simpa (disch := decide) only [L2, L1, store_get_ne] using hb.offset))) ?_
  · simp (disch := decide) only [evalExpr?, L3, L2, L1, readLocalPath?, store_get_ne, hb.offset, hbody,
      EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp_add_int_ok, Int.natCast_add, Int.ofNat_eq_natCast]
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := .int (Int.ofNat (i+1))) ?_
    (assignLocalBase_ok (frame := {contract := contract, locals := L3, immutables := imms})
      (by simpa (disch := decide) only [L3, L2, L1, store_get_ne] using hb.index))) ExecBlock.nil
  simp (disch := decide) only [evalExpr?, L3, L2, L1, store_get_ne, hb.index,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp_add_int_ok, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]



theorem encodeArrayResult_eval {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {heap : Nat} (h : EncodeArrayInv locals ats heap ats.length)
    (hlen : ats.length < UInt256.size) :
    evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm encodeArrayResult =
      .ok (.bytes (attestationArrayEncoding ats)) := by
  apply evalPackedBytes
  have hl : encodePackedValue? abiUInt256 (.int (Int.ofNat ats.length)) =
      some (EVM.Word.toBytesBE (UInt256.ofNat ats.length)) := by
    simpa only [ulit_toNat' _ hlen] using encodePacked_uint256 (UInt256.ofNat ats.length)
  have he := evalPackedArgs_cons
    (show evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
      (.arrayLength .localVar {base := "attestations"}) = .ok (.int (Int.ofNat ats.length)) by
        simp only [evalExpr?, readLocalPath?, h.attestations, List.length_map, EvalResult.bind, bind, pure, Int.ofNat_eq_natCast]) hl
    (evalPackedArgs_cons
      (show evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm (.var "heads") =
        .ok (.bytes (wordBytes (attestationArrayHeads ats ats.length))) by simp only [evalExpr?, h.heads, EvalResult.ofOption])
      (encodePacked_dynamic_bytes _)
      (evalPackedArgs_single
        (show evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm (.var "tails") =
          .ok (.bytes (attestationArrayBodies ats ats.length)) by simp only [evalExpr?, h.tails, EvalResult.ofOption])
        (encodePacked_dynamic_bytes _)))
  simpa only [attestationArrayEncoding, wordBytes, byteArray_toList_eq, ByteArray.data_append,
    Array.toList_append, toByteArray_eq_toBytesBE, List.append_assoc] using he

theorem encodeArrayLoop_exec {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {heap : Nat} (h : EncodeArrayInv locals ats heap 0)
    (hdata : ∀ a ∈ ats, a.data.size < UInt256.size)
    (hbound : attestationArrayOffset ats ats.length < UInt256.size) :
    ∃ locals', ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.while encodeArrayGuard encodeArrayIteration)
      (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
      EncodeArrayInv locals' ats heap ats.length := by
  let P := fun n L => ∃ i, i+n=ats.length ∧ EncodeArrayInv L ats heap i
  have hf : ∀ L, P 0 L → evalExpr? cfg {contract := contract, locals := L, immutables := imms} evm encodeArrayGuard = .ok (.bool false) := by
    rintro L ⟨i, hi, hinv⟩
    have he := encodeArrayGuard_eval (cfg := cfg) (imms := imms) (evm := evm) hinv
    have hi0 : i = ats.length := by omega
    subst i
    simpa only [Nat.lt_irrefl, decide_false] using he
  have ht : ∀ n L, P (n+1) L → evalExpr? cfg {contract := contract, locals := L, immutables := imms} evm encodeArrayGuard = .ok (.bool true) := by
    rintro n L ⟨i, hi, hinv⟩
    have hi' : i < ats.length := by omega
    simpa only [hi', decide_true] using encodeArrayGuard_eval (cfg := cfg) (imms := imms) (evm := evm) hinv
  have hs : ∀ n L, P (n+1) L → ∃ L',
      ExecBlock fork cfg {contract := contract, locals := L, immutables := imms} evm encodeArrayIteration
        (.ok {contract := contract, locals := L', immutables := imms} evm) ∧ P n L' := by
    rintro n L ⟨i, hi, hinv⟩
    have hi' : i < ats.length := by omega
    refine ⟨encodeArrayNext L ats heap i ats[i], encodeArrayIteration_exec hinv hi'
      (hdata _ (List.getElem_mem hi')) (lt_of_le_of_lt (attestationArrayOffset_le ats i) hbound), i+1, ?_, encodeArrayNext_inv hinv hi'⟩
    omega
  obtain ⟨L, hl, i, hi, hinv⟩ := execWhile_var P hf ht hs ats.length locals ⟨0, by omega, h⟩
  have hi' : i = ats.length := by omega
  exact ⟨L, hl, hi' ▸ hinv⟩

theorem encodeAttestationsSource {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {heap : Nat}
    (ha : locals.get? "attestations" = some (.array (ats.map AttestationRecord.value)))
    (hh : locals.get? "$EAS.freeMemory" = some (.int (Int.ofNat heap)))
    (hdata : ∀ a ∈ ats, a.data.size < UInt256.size)
    (hbound : attestationArrayOffset ats ats.length < UInt256.size) :
    ∃ locals', ExecFuncBody fork cfg {contract := contract, locals := locals, immutables := imms} evm encodeAttestationsFunction.body
      (.returned {contract := contract, locals := locals', immutables := imms} evm
        (some [.bytes (attestationArrayEncoding ats), .int (Int.ofNat heap)])) := by
  obtain ⟨L, hl, hinv⟩ := encodeArrayLoop_exec (cfg := cfg) (imms := imms) (evm := evm) (encodeArrayInit_inv ha hh) hdata hbound
  have hlen : ats.length < UInt256.size := by unfold attestationArrayOffset at hbound; omega
  refine ⟨L, ?_⟩
  rw [encodeAttestations_body]
  apply execFuncBody_append (encodeArrayInit_exec ha)
  apply ExecFuncBody.execBlockRet
  apply ExecBlock.consNormal hl
  apply ExecBlock.consReturn
  apply ExecStmt.return
  simp only [evalExprs?, encodeArrayResult_eval hinv hlen, evalExpr?, hinv.heap,
    EvalResult.ofOption, EvalResult.bind, bind, pure]

def encodeAttestationsArgs (ats : List AttestationRecord) (heap : Nat) : Store :=
  (∅ : Store) |>.insert "$EAS.freeMemory" (.int (Int.ofNat heap))
    |>.insert "attestations" (.array (ats.map AttestationRecord.value))

theorem encodeAttestations_lookup : lookupCallable? contract "_encodeAttestations" = some encodeAttestationsFunction.toCallable := by rfl

theorem encodeAttestations_bind (ats : List AttestationRecord) (heap : Nat) :
    bindParams? encodeAttestationsFunction.params [.array (ats.map AttestationRecord.value), .int (Int.ofNat heap)] =
      some (encodeAttestationsArgs ats heap) := by rfl

theorem encodeAttestationsCall {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {ats : List AttestationRecord} {heap : Nat} {args : List Expr} {retVar : Ident}
    (he : evalExprs? cfg {contract := contract, locals := locals, immutables := imms} evm args =
      .ok [.array (ats.map AttestationRecord.value), .int (Int.ofNat heap)])
    (hdata : ∀ a ∈ ats, a.data.size < UInt256.size)
    (hbound : attestationArrayOffset ats ats.length < UInt256.size) :
    ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.internalCall "_encodeAttestations" args retVar)
      (.ok {contract := contract, locals := locals.insert retVar (.tuple [
        .bytes (attestationArrayEncoding ats), .int (Int.ofNat heap)]), immutables := imms} evm) := by
  obtain ⟨L, hs⟩ := encodeAttestationsSource (cfg := cfg) (imms := imms) (evm := evm) (heap := heap)
    (store_get_self _ _ _ : (encodeAttestationsArgs ats heap).get? "attestations" = _)
    (by simp only [encodeAttestationsArgs, store_get_ne _ _ (by decide : ("attestations" == "$EAS.freeMemory") = false), store_get_self])
    hdata hbound
  exact internalCallFunctionReturn he encodeAttestations_lookup (encodeAttestations_bind ats heap) hs

end Benchmarks.EAS.EAS
