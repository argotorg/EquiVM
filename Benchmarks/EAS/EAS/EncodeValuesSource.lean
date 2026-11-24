import Benchmarks.EAS.EAS.ArrayEncoding

variable {fork : Ethereum.Fork}
open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.EAS.EAS
set_option maxRecDepth 10000

-- The uint256-array encoder in the batched resolver; unrelated locals are framed through its loop.
def encodeValuesGuard : Expr := .binary .lt (.var "i") (.arrayLength .localVar {base := "values"})
def encodeValuesIteration : Body := [
  .assign .localVar {base := "valuesBody"} (.abiEncodePacked [
    (.bytes, .var "valuesBody"), (abiUInt256, .index (.var "values") (.var "i"))]),
  .assign .localVar {base := "i"} (.binary .add (.var "i") (.intLit 1))]
def encodeValuesBlock : Body := [
  .letDecl "valuesBody" (some .bytes) (.abiEncodePacked [(abiUInt256, .arrayLength .localVar {base := "values"})]),
  .letDecl "i" (some abiUInt256) (.intLit 0),
  .while encodeValuesGuard encodeValuesIteration]

def valuesEncoding (words : List UInt256) (i : Nat) : ByteArray :=
  wordBytes (UInt256.ofNat words.length :: words.take i)

structure EncodeValuesInv (base locals : Store) (words : List UInt256) (i : Nat) : Prop where
  values : locals.get? "values" = some (.array (words.map fun w => .int (Int.ofNat w.toNat)))
  encoded : locals.get? "valuesBody" = some (.bytes (valuesEncoding words i))
  index : locals.get? "i" = some (.int (Int.ofNat i))
  preserved : ∀ key, ("valuesBody" == key) = false → ("i" == key) = false → locals.get? key = base.get? key

def encodeValuesNext (locals : Store) (words : List UInt256) (i : Nat) : Store :=
  locals |>.insert "valuesBody" (.bytes (valuesEncoding words (i+1))) |>.insert "i" (.int (Int.ofNat (i+1)))

theorem encodeValuesNext_inv {base locals : Store} {words : List UInt256} {i : Nat}
    (h : EncodeValuesInv base locals words i) : EncodeValuesInv base (encodeValuesNext locals words i) words (i+1) := by
  constructor
  · simp (disch := decide) only [encodeValuesNext, store_get_ne, h.values]
  · simp (disch := decide) only [encodeValuesNext, store_get_ne, store_get_self]
  · exact store_get_self _ _ _
  · intro key hb hi
    simp only [encodeValuesNext, store_get_ne _ _ hi, store_get_ne _ _ hb, h.preserved key hb hi]

theorem encodeValuesGuard_eval {cfg : Config} {base locals imms : Store} {evm : EVM.State}
    {words : List UInt256} {i : Nat} (h : EncodeValuesInv base locals words i) :
    evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm encodeValuesGuard =
      .ok (.bool (decide (i < words.length))) := by
  simp only [encodeValuesGuard, evalExpr?, h.index, readLocalPath?, h.values,
    List.length_map, EvalResult.ofOption, EvalResult.bind, bind, evalBinaryOp_lt_int_ok,
    Int.ofNat_eq_natCast, Nat.cast_lt]

theorem encodeValuesIteration_exec {cfg : Config} {base locals imms : Store} {evm : EVM.State}
    {words : List UInt256} {i : Nat} (h : EncodeValuesInv base locals words i) (hi : i < words.length) :
    ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm encodeValuesIteration
      (.ok {contract := contract, locals := encodeValuesNext locals words i, immutables := imms} evm) := by
  have hw : lookupNth? words i = some words[i] := (lookupNth_getElem words i).trans (List.getElem?_eq_getElem hi)
  have hx : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
      (.index (.var "values") (.var "i")) = .ok (.int (Int.ofNat words[i].toNat)) := by
    simp only [evalExpr?, h.values, h.index, EvalResult.ofOption, EvalResult.bind, bind,
      evalIndex?, Int.ofNat_eq_natCast, Int.natCast_nonneg, List.length_map, Nat.cast_lt, hi,
      and_self, if_true, Int.toNat_natCast, lookupNth_map, hw, Option.map_some, normalizeRawBoolWord?]
  have he : evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
      (.abiEncodePacked [(.bytes, .var "valuesBody"), (abiUInt256, .index (.var "values") (.var "i"))]) =
      .ok (.bytes (valuesEncoding words (i+1))) := by
    apply evalPackedBytes
    have hp := evalPackedArgs_cons
      (show evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm (.var "valuesBody") =
        .ok (.bytes (valuesEncoding words i)) by simp only [evalExpr?, h.encoded, EvalResult.ofOption])
      (encodePacked_dynamic_bytes _) (evalPackedArgs_single hx (encodePacked_uint256 words[i]))
    have hs : valuesEncoding words (i+1) = valuesEncoding words i ++ words[i].toByteArray := by
      simp only [valuesEncoding, List.take_succ_eq_append_getElem hi, ← List.cons_append, wordBytes_append,
        wordBytes, ByteArray.append_empty, ByteArray.append_assoc]
    simpa only [hs, byteArray_toList_eq, ByteArray.data_append, Array.toList_append, toByteArray_eq_toBytesBE] using hp
  apply ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) he (assignLocalBase_ok h.encoded))
  refine ExecBlock.consNormal (ExecStmt.assign (fork := fork) (hperm := by first | exact Or.inl rfl | assumption | exact Or.inr ‹_›) (value := .int (Int.ofNat (i+1))) ?_
    (assignLocalBase_ok (frame := {contract := contract, locals := locals.insert "valuesBody" (.bytes (valuesEncoding words (i+1))), immutables := imms})
      (by simpa (disch := decide) only [store_get_ne] using h.index))) ExecBlock.nil
  simp (disch := decide) only [evalExpr?, store_get_ne, h.index,
    EvalResult.ofOption, EvalResult.bind, bind, pure, evalBinaryOp_add_int_ok, Int.ofNat_eq_natCast, Nat.cast_add, Nat.cast_one]

theorem encodeValuesLoop_exec {cfg : Config} {base locals imms : Store} {evm : EVM.State}
    {words : List UInt256} (h : EncodeValuesInv base locals words 0) :
    ∃ locals', ExecStmt fork cfg {contract := contract, locals := locals, immutables := imms} evm
      (.while encodeValuesGuard encodeValuesIteration)
      (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
      EncodeValuesInv base locals' words words.length := by
  let P := fun n L => ∃ i, i+n=words.length ∧ EncodeValuesInv base L words i
  have hf : ∀ L, P 0 L → evalExpr? cfg {contract := contract, locals := L, immutables := imms} evm encodeValuesGuard = .ok (.bool false) := by
    rintro L ⟨i, hi, hinv⟩
    have hi0 : i = words.length := by omega
    subst i
    simpa only [Nat.lt_irrefl, decide_false] using encodeValuesGuard_eval (cfg := cfg) (imms := imms) (evm := evm) hinv
  have ht : ∀ n L, P (n+1) L → evalExpr? cfg {contract := contract, locals := L, immutables := imms} evm encodeValuesGuard = .ok (.bool true) := by
    rintro n L ⟨i, hi, hinv⟩
    have hi' : i < words.length := by omega
    simpa only [hi', decide_true] using encodeValuesGuard_eval (cfg := cfg) (imms := imms) (evm := evm) hinv
  have hs : ∀ n L, P (n+1) L → ∃ L',
      ExecBlock fork cfg {contract := contract, locals := L, immutables := imms} evm encodeValuesIteration
        (.ok {contract := contract, locals := L', immutables := imms} evm) ∧ P n L' := by
    rintro n L ⟨i, hi, hinv⟩
    refine ⟨encodeValuesNext L words i, encodeValuesIteration_exec hinv (by omega), i+1, by omega, encodeValuesNext_inv hinv⟩
  obtain ⟨L, hl, i, hi, hinv⟩ := execWhile_var P hf ht hs words.length locals ⟨0, by omega, h⟩
  have hi' : i = words.length := by omega
  exact ⟨L, hl, hi' ▸ hinv⟩

theorem encodeValuesBlock_exec {cfg : Config} {locals imms : Store} {evm : EVM.State}
    {words : List UInt256}
    (hv : locals.get? "values" = some (.array (words.map fun w => .int (Int.ofNat w.toNat))))
    (hlen : words.length < UInt256.size) :
    ∃ locals', ExecBlock fork cfg {contract := contract, locals := locals, immutables := imms} evm encodeValuesBlock
      (.ok {contract := contract, locals := locals', immutables := imms} evm) ∧
      EncodeValuesInv locals locals' words words.length := by
  let L := (locals.insert "valuesBody" (.bytes (valuesEncoding words 0))).insert "i" (.int (Int.ofNat 0))
  have hinv : EncodeValuesInv locals L words 0 := by
    constructor
    · simp (disch := decide) only [L, store_get_ne, hv]
    · simp (disch := decide) only [L, store_get_ne, store_get_self]
    · exact store_get_self _ _ _
    · intro key hb hi
      simp only [L, store_get_ne _ _ hi, store_get_ne _ _ hb]
  obtain ⟨L', hl, hinv'⟩ := encodeValuesLoop_exec (cfg := cfg) (imms := imms) (evm := evm) hinv
  refine ⟨L', ?_, hinv'⟩
  refine ExecBlock.consNormal (ExecStmt.letDecl (value := .bytes (valuesEncoding words 0)) ?_) ?_
  · apply evalPackedBytes
    have hp := evalPackedArgs_single
      (show evalExpr? cfg {contract := contract, locals := locals, immutables := imms} evm
        (.arrayLength .localVar {base := "values"}) = .ok (.int (Int.ofNat words.length)) by
          simp only [evalExpr?, readLocalPath?, hv, List.length_map, EvalResult.bind, bind, pure, Int.ofNat_eq_natCast])
      (by simpa only [ulit_toNat' _ hlen] using encodePacked_uint256 (UInt256.ofNat words.length))
    simpa only [valuesEncoding, List.take_zero, wordBytes, ByteArray.append_empty, byteArray_toList_eq, toByteArray_eq_toBytesBE, List.toList_toArray] using hp
  apply ExecBlock.consNormal (ExecStmt.letDecl (value := .int (Int.ofNat 0)) (by simp only [evalExpr?, pure]; rfl))
  exact ExecBlock.consNormal hl ExecBlock.nil

end Benchmarks.EAS.EAS
