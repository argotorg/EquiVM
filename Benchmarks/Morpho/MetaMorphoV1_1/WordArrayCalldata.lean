import Benchmarks.Morpho.MetaMorphoV1_1.DynamicCalldata
import Benchmarks.EAS.Attester.WordArrayABI
import Benchmarks.EAS.Attester.LocalArray

/-! Canonical bytes32 arrays decoded from calldata, with complete boundary checks. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

open Benchmarks.EAS.Attester (ArrayHeadChecks arrayHead arrayHead_toNat)

-- LIBRARY CANDIDATE: the single-word-array ABI layout, independent of this contract.
def calldataArrayOffset (cd : ByteArray) : Nat := (calldataWord cd 4).toNat

def calldataArrayLength (cd : ByteArray) : Nat :=
  (calldataWord cd (4 + calldataArrayOffset cd)).toNat

def calldataArrayValues (cd : ByteArray) : List Value :=
  wordArrayValues (fun i ↦ calldataWord cd (calldataArrayOffset cd + 36 + 32 * i))
    0 (calldataArrayLength cd)

structure WordArrayCalldataChecks (cd : ByteArray) : Prop where
  head : 36 ≤ cd.size
  size : cd.size < 2 ^ 255
  offset : calldataArrayOffset cd ≤ solcMaxU64
  lengthWord : calldataArrayOffset cd + 36 ≤ cd.size
  length : calldataArrayLength cd ≤ solcMaxU64
  data : calldataArrayOffset cd + 36 + 32 * calldataArrayLength cd ≤ cd.size

theorem WordArrayCalldataChecks.runtime {cd : ByteArray} (hc : WordArrayCalldataChecks cd) :
    ArrayHeadChecks cd (arrayHead cd 4) := by
  apply ArrayHeadChecks.of_bounds hc.size
  · rw [arrayHead_toNat hc.offset]
    exact hc.length
  · rw [arrayHead_toNat hc.offset]
    have h := hc.data
    change (calldataWord cd 4).toNat + 36 +
      32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤ cd.size at h
    omega

theorem wordArrayCalldataChecks_of_runtime {cd : ByteArray}
    (hhead : 36 ≤ cd.size) (hsize : cd.size < UInt256.size)
    (hoff : (calldataWord cd 4).toNat ≤ solcMaxU64)
    (hc : ArrayHeadChecks cd (arrayHead cd 4)) : WordArrayCalldataChecks cd := by
  have hsign : cd.size < 2 ^ 255 := by
    by_contra hh
    exact hc.header (calldataStart_slt_zero_of_size_high cd (Nat.not_lt.mpr hoff) hsize hh)
  have hlen := uint64Bound_of_isZero_gt hc.length
  have hdata := hc.outer_bounds hoff hsize
  rw [arrayHead_toNat hoff] at hlen hdata
  refine ⟨hhead, hsign, hoff, ?_, hlen, ?_⟩
  · change (calldataWord cd 4).toNat + 36 ≤ cd.size
    omega
  · change (calldataWord cd 4).toNat + 36 +
      32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤ cd.size
    omega

theorem calldataArrayValues_length (cd : ByteArray) :
    (calldataArrayValues cd).length = calldataArrayLength cd := wordArrayValues_length _ _ _

theorem calldataArrayValues_getElem (cd : ByteArray) (i : Nat)
    (hi : i < calldataArrayLength cd) :
    (calldataArrayValues cd)[i]? = some
      (wordBytes32Value (calldataWord cd (calldataArrayOffset cd + 36 + 32 * i))) := by
  simpa only [Nat.zero_add] using wordArrayValues_getElem
    (fun i ↦ calldataWord cd (calldataArrayOffset cd + 36 + 32 * i)) 0 _ i hi

-- LIBRARY CANDIDATE: decoding any elementary ABI array implies the same calldata bounds.
theorem elemArrayCalldata_facts {elem : ElemType} {cd : ByteArray} {value : Value}
    (hd : decodeSingleDynamic? (.dynamicArray (.elem elem)) cd = some value) :
    ∃ values ending, value = .array values ∧ WordArrayCalldataChecks cd ∧
      decodeABIValue? (.dynamicArray (.elem elem)) (cd.toList.drop 4) (calldataArrayOffset cd) =
        some (.array values, ending) ∧ values.length = calldataArrayLength cd := by
  obtain ⟨ending, hhead, hsize, hoff, hv⟩ := decodeSingleDynamic_facts hd
  obtain ⟨values, hvalues⟩ := decodeABIValue_dynamicArray_is_array hv
  rw [hvalues] at hv
  obtain ⟨len, hr, hlen, he, hb, hlength⟩ := decodeABIValue_dynamicArray_elem32_facts hv
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  have hread := readNat?_some_length hr
  rw [List.length_drop, hl] at hread hb
  rw [readNat_drop4_dynamic_eq_calldataWord (by omega), Option.some.injEq] at hr
  have hcount : len = calldataArrayLength cd := hr.symm
  subst len
  exact ⟨values, ending, hvalues, ⟨hhead, hsize, hoff, by
    change (calldataWord cd 4).toNat + 36 ≤ cd.size; omega,
    by omega, by change (calldataWord cd 4).toNat + 36 + _ ≤ cd.size; omega⟩, hv, hlength⟩

theorem wordArrayCalldata_facts {cd : ByteArray} {value : Value}
    (hd : decodeSingleDynamic? (.dynamicArray abiBytes32) cd = some value) :
    ∃ values ending, value = .array values ∧ WordArrayCalldataChecks cd ∧
      decodeABIValue? (.dynamicArray abiBytes32) (cd.toList.drop 4) (calldataArrayOffset cd) =
        some (.array values, ending) ∧ values.length = calldataArrayLength cd :=
  elemArrayCalldata_facts hd

theorem wordArrayCalldata_lookup {cd : ByteArray} {values : List Value} {ending i : Nat}
    (hd : decodeABIValue? (.dynamicArray abiBytes32) (cd.toList.drop 4)
      (calldataArrayOffset cd) = some (.array values, ending)) (hi : i < values.length) :
    values[i]? = some
      (wordBytes32Value (calldataWord cd (calldataArrayOffset cd + 36 + 32 * i))) := by
  obtain ⟨word, hv⟩ := decodeABIValue_dynamicArray_bytes32_lookup_shape hd hi
  have hr := decodeABIValue_dynamicArray_bytes32_lookup_readNat hd hv
  have hb := readNat?_some_length hr
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  rw [List.length_drop, hl] at hb
  rw [readNat_drop4_at_eq_calldataWord _ (by omega), Option.some.injEq] at hr
  have he : word = calldataWord cd (calldataArrayOffset cd + 36 + 32 * i) := by
    apply u256_inj
    simpa only [show 4 + (calldataArrayOffset cd + 32 + 32 * i) =
      calldataArrayOffset cd + 36 + 32 * i by omega] using hr.symm
  simpa only [lookupNth_eq_getElem, he] using hv

theorem wordArrayCalldata_ok {cd : ByteArray} (hc : WordArrayCalldataChecks cd) :
    decodeSingleDynamic? (.dynamicArray abiBytes32) cd =
      some (.array (calldataArrayValues cd)) := by
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  obtain ⟨values, hv, hlen⟩ := decodeABIValue_dynamicArray_bytes32_exists
    (readNat_drop4_dynamic_eq_calldataWord (by
      have h := hc.lengthWord
      change 4 + calldataArrayOffset cd + 32 ≤ cd.size
      omega)) (Nat.not_lt.mpr hc.length)
    (by
      rw [List.length_drop, hl]
      change calldataArrayOffset cd + 32 + 32 * calldataArrayLength cd ≤ cd.size - 4
      have h := hc.data
      omega)
  change values.length = calldataArrayLength cd at hlen
  have he : values = calldataArrayValues cd := by
    apply List.ext_getElem (by rw [calldataArrayValues, wordArrayValues_length]; exact hlen)
    intro i hi hi'
    have hl := wordArrayCalldata_lookup hv hi
    have hr := wordArrayValues_getElem
      (fun i ↦ calldataWord cd (calldataArrayOffset cd + 36 + 32 * i))
      0 (calldataArrayLength cd) i (by omega)
    simp only [Nat.zero_add] at hr
    change (calldataArrayValues cd)[i]? = _ at hr
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hl
    rw [List.getElem?_eq_getElem hi', Option.some.injEq] at hr
    exact hl.trans hr.symm
  have hoff : ¬ solcMaxU64 < (calldataWord cd 4).toNat := Nat.not_lt.mpr hc.offset
  simp only [decodeSingleDynamic?, Nat.not_lt.mpr hc.head, Nat.not_le.mpr hc.size,
    false_or, if_false, hoff, hv, bind, Option.bind, he]

theorem wordArrayCalldata_bad {cd : ByteArray} (hc : ¬ WordArrayCalldataChecks cd) :
    decodeSingleDynamic? (.dynamicArray abiBytes32) cd = none := by
  cases hd : decodeSingleDynamic? (.dynamicArray abiBytes32) cd with
  | none => rfl
  | some value =>
      obtain ⟨_, _, _, hchecks, _, _⟩ := wordArrayCalldata_facts hd
      exact False.elim (hc hchecks)

theorem decodeCalldataWordArray {cd : ByteArray} (name : Ident)
    (hc : WordArrayCalldataChecks cd) :
    decodeCalldata [name] [.dynamicArray abiBytes32] cd =
      some ((∅ : Store).insert name (.array (calldataArrayValues cd))) := by
  rw [decodeCalldata_single_dynamic _ _ _ rfl, wordArrayCalldata_ok hc]
  rfl

theorem decodeCalldataWordArrayBad {cd : ByteArray} (name : Ident)
    (hc : ¬ WordArrayCalldataChecks cd) :
    decodeCalldata [name] [.dynamicArray abiBytes32] cd = none := by
  rw [decodeCalldata_single_dynamic _ _ _ rfl, wordArrayCalldata_bad hc]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1
