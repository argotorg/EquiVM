import Benchmarks.EAS.Attester.ArrayABI
import Benchmarks.EAS.Attester.WordArrayABI
import Benchmarks.EAS.Attester.LocalArray

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

theorem readNat_at_eq_calldataWord {out : ByteArray} (off : Nat) (hin : off + 32 ≤ out.size) :
    readNat? out.toList off = some (calldataWord out off).toNat := by
  have hl : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hread : readBytes? out.toList off 32 = some ((out.toList.drop off).take 32) := by
    unfold readBytes?
    rw [if_pos (by rw [List.length_take, List.length_drop, hl]; omega)]
  rw [readNat?, readWord?, hread]
  simp only [bind, Option.bind, decode_word_at_eq_any out off hin]
  rfl

theorem decodedReturnBytes32Array_lookup {out : ByteArray} {values : List Value}
    {start endOffset i : Nat}
    (hd : decodeABIValue? (.dynamicArray abiBytes32) out.toList start =
      some (.array values, endOffset)) (hi : i < values.length) :
    values[i]? = some (wordBytes32Value (calldataWord out (start + 32 + 32 * i))) := by
  obtain ⟨word, hv⟩ := decodeABIValue_dynamicArray_bytes32_lookup_shape hd hi
  have hr := decodeABIValue_dynamicArray_bytes32_lookup_readNat hd hv
  have hb := readNat?_some_length hr
  have hl : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [hl] at hb
  rw [readNat_at_eq_calldataWord _ hb, Option.some.injEq] at hr
  have he : word = calldataWord out (start + 32 + 32 * i) := u256_inj hr.symm
  simpa only [lookupNth_eq_getElem, he] using hv

end Reasoning.Theory

namespace Benchmarks.EAS.Attester

def returnArrayOffset (out : ByteArray) : Nat := (calldataWord out 0).toNat

def returnArrayCount (out : ByteArray) : Nat := (calldataWord out (returnArrayOffset out)).toNat

def returnArrayValues (out : ByteArray) : List Value :=
  wordArrayValues (fun i ↦ calldataWord out (returnArrayOffset out + 32 + 32 * i))
    0 (returnArrayCount out)

structure ReturnArrayChecks (out : ByteArray) : Prop where
  head : 32 ≤ out.size
  offset : returnArrayOffset out ≤ solcMaxU64
  lengthWord : returnArrayOffset out + 32 ≤ out.size
  length : returnArrayCount out ≤ solcMaxU64
  data : returnArrayOffset out + 32 + 32 * returnArrayCount out ≤ out.size

theorem returnArrayDecode_eq {out : ByteArray} (hhi : out.size < 2 ^ 255) :
    decodeReturnValue? bytes32Array out = (do
      let off ← readNat? out.toList 0
      if solcMaxU64 < off then none else do
      let value ← decodeABIValue? bytes32Array out.toList off
      some value.1) := by
  have hl : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  simp only [decodeReturnValue?, decodeReturnValues?, List.isEmpty_cons, Bool.false_eq_true,
    true_and, hl, Nat.not_le.mpr hhi, if_false,
    show abiTupleHeadSize? [bytes32Array] = some 32 by native_decide,
    bind, Option.bind, decodeABIValues?,
    show isDynamicABIType bytes32Array = true from rfl, if_true, Nat.zero_add,
    solcMaxLen_modern]
  cases hr : readNat? out.toList 0 with
  | none => rfl
  | some off =>
      by_cases ho : solcMaxU64 < off
      · simp only [ho, if_true, Option.bind_none]
      · simp only [ho, if_false]
        cases hd : decodeABIValue? bytes32Array out.toList off with
        | none => rfl
        | some value => rcases value with ⟨value, ending⟩; rfl

theorem returnArrayDecode_some_facts {out : ByteArray} {value : Value}
    (hhi : out.size < 2 ^ 255) (hd : decodeReturnValue? bytes32Array out = some value) :
    ∃ values ending, value = .array values ∧
      decodeABIValue? bytes32Array out.toList (returnArrayOffset out) =
        some (.array values, ending) ∧ ReturnArrayChecks out ∧
      values.length = returnArrayCount out := by
  have hl : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [returnArrayDecode_eq hhi] at hd
  cases hr : readNat? out.toList 0 with
  | none => simp only [hr, bind, Option.bind] at hd; cases hd
  | some off =>
      simp only [hr, bind, Option.bind] at hd
      by_cases ho : solcMaxU64 < off
      · simp only [ho, if_true] at hd; cases hd
      simp only [ho, if_false] at hd
      cases ha : decodeABIValue? bytes32Array out.toList off with
      | none => simp only [ha, Option.bind_none] at hd; cases hd
      | some pair =>
          rcases pair with ⟨value0, ending⟩
          simp only [ha, Option.bind_some, Option.some.injEq] at hd
          obtain ⟨values, hv⟩ := decodeABIValue_dynamicArray_is_array ha
          have hh := readNat?_some_length hr
          rw [hl] at hh
          rw [readNat_at_eq_calldataWord _ (by omega), Option.some.injEq] at hr
          have hoff : off = returnArrayOffset out := hr.symm
          subst off
          rw [hv] at ha
          obtain ⟨n, hn, hn64, he, heb, hlen⟩ := decodeABIValue_dynamicArray_elem32_facts ha
          have hnb := readNat?_some_length hn
          rw [hl] at hnb heb
          rw [readNat_at_eq_calldataWord _ hnb, Option.some.injEq] at hn
          have hc : n = returnArrayCount out := hn.symm
          subst n
          exact ⟨values, ending, hd ▸ hv, ha,
            ⟨by omega, by omega, hnb, by omega, by omega⟩, hlen⟩

theorem returnArrayDecode_exists {out : ByteArray} (hhi : out.size < 2 ^ 255)
    (hc : ReturnArrayChecks out) :
    ∃ values ending, decodeReturnValue? bytes32Array out = some (.array values) ∧
      decodeABIValue? bytes32Array out.toList (returnArrayOffset out) =
        some (.array values, ending) ∧ values.length = returnArrayCount out := by
  have hl : out.toList.length = out.size := by rw [byteArray_toList_eq, Array.length_toList]; rfl
  obtain ⟨values, hv, hlen⟩ := decodeABIValue_dynamicArray_bytes32_exists
    (readNat_at_eq_calldataWord (returnArrayOffset out) hc.lengthWord)
    (Nat.not_lt.mpr hc.length) (by rw [hl]; exact hc.data)
  change decodeABIValue? bytes32Array out.toList (returnArrayOffset out) = _ at hv
  refine ⟨values, _, ?_, hv, hlen⟩
  rw [returnArrayDecode_eq hhi, readNat_at_eq_calldataWord 0 (by simpa using hc.head)]
  change (if solcMaxU64 < returnArrayOffset out then none else
    (decodeABIValue? bytes32Array out.toList (returnArrayOffset out)).bind
      (fun p ↦ some p.1)) = _
  rw [if_neg (Nat.not_lt.mpr hc.offset), hv]
  rfl

theorem returnArrayDecode_bad {out : ByteArray} (hhi : out.size < 2 ^ 255)
    (hc : ¬ ReturnArrayChecks out) : decodeReturnValue? bytes32Array out = none := by
  cases hd : decodeReturnValue? bytes32Array out with
  | none => rfl
  | some value =>
      obtain ⟨_, _, _, _, hcheck, _⟩ := returnArrayDecode_some_facts hhi hd
      exact False.elim (hc hcheck)

theorem returnArrayDecode_ok {out : ByteArray} (hhi : out.size < 2 ^ 255)
    (hc : ReturnArrayChecks out) :
    decodeReturnValue? bytes32Array out = some (.array (returnArrayValues out)) := by
  obtain ⟨values, ending, hd, hv, hlen⟩ := returnArrayDecode_exists hhi hc
  have he : values = returnArrayValues out := by
    apply List.ext_getElem (by rw [returnArrayValues, wordArrayValues_length]; exact hlen)
    intro i hi hi'
    have hl := decodedReturnBytes32Array_lookup hv hi
    have hr := wordArrayValues_getElem
      (fun i ↦ calldataWord out (returnArrayOffset out + 32 + 32 * i))
      0 (returnArrayCount out) i (by omega)
    simp only [Nat.zero_add] at hr
    change (returnArrayValues out)[i]? = _ at hr
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hl
    rw [List.getElem?_eq_getElem hi', Option.some.injEq] at hr
    exact hl.trans hr.symm
  simpa only [he] using hd

end Benchmarks.EAS.Attester
