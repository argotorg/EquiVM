import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayCalldata

/-! Canonical uint256 arrays decoded from calldata, using the common word-array bounds. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: the uint256 interpretation of a sequence of ABI words.
def uintArrayValues (words : Nat → UInt256) (i n : Nat) : List Value :=
  (wordArrayWords words i n).map uint256Value

theorem uintArrayValues_length (words : Nat → UInt256) (i n : Nat) :
    (uintArrayValues words i n).length = n := by
  simp only [uintArrayValues, List.length_map, wordArrayWords_length]

theorem uintArrayValues_getElem (words : Nat → UInt256) (i n k : Nat) (hk : k < n) :
    (uintArrayValues words i n)[k]? = some (uint256Value (words (i + k))) := by
  simp only [uintArrayValues, List.getElem?_map, wordArrayWords_getElem _ _ _ _ hk,
    Option.map_some]

def calldataUintArrayValues (cd : ByteArray) : List Value :=
  uintArrayValues (fun i ↦ calldataWord cd (calldataArrayOffset cd + 36 + 32 * i))
    0 (calldataArrayLength cd)

theorem calldataUintArrayValues_length (cd : ByteArray) :
    (calldataUintArrayValues cd).length = calldataArrayLength cd := uintArrayValues_length _ _ _

theorem calldataUintArrayValues_getElem (cd : ByteArray) (i : Nat)
    (hi : i < calldataArrayLength cd) :
    (calldataUintArrayValues cd)[i]? = some
      (uint256Value (calldataWord cd (calldataArrayOffset cd + 36 + 32 * i))) := by
  simpa only [Nat.zero_add] using uintArrayValues_getElem
    (fun i ↦ calldataWord cd (calldataArrayOffset cd + 36 + 32 * i)) 0 _ i hi

theorem uintArrayCalldata_lookup {cd : ByteArray} {values : List Value} {ending i : Nat}
    (hd : decodeABIValue? (.dynamicArray abiUInt256) (cd.toList.drop 4)
      (calldataArrayOffset cd) = some (.array values, ending)) (hi : i < values.length) :
    values[i]? = some
      (uint256Value (calldataWord cd (calldataArrayOffset cd + 36 + 32 * i))) := by
  obtain ⟨word, hv⟩ := decodeABIValue_dynamicArray_uint256_lookup_shape hd hi
  have hr := decodeABIValue_dynamicArray_uint256_lookup_readNat hd hv
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

theorem uintArrayCalldata_ok {cd : ByteArray} (hc : WordArrayCalldataChecks cd) :
    decodeSingleDynamic? (.dynamicArray abiUInt256) cd =
      some (.array (calldataUintArrayValues cd)) := by
  have hl : cd.toList.length = cd.size := by
    rw [byteArray_toList_eq, Array.length_toList]; rfl
  obtain ⟨values, hv, hlen⟩ := decodeABIValue_dynamicArray_uint256_exists
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
  have he : values = calldataUintArrayValues cd := by
    apply List.ext_getElem (by rw [calldataUintArrayValues, uintArrayValues_length]; exact hlen)
    intro i hi hi'
    have hl := uintArrayCalldata_lookup hv hi
    have hr := uintArrayValues_getElem
      (fun i ↦ calldataWord cd (calldataArrayOffset cd + 36 + 32 * i))
      0 (calldataArrayLength cd) i (by omega)
    simp only [Nat.zero_add] at hr
    change (calldataUintArrayValues cd)[i]? = _ at hr
    rw [List.getElem?_eq_getElem hi, Option.some.injEq] at hl
    rw [List.getElem?_eq_getElem hi', Option.some.injEq] at hr
    exact hl.trans hr.symm
  have hoff : ¬ solcMaxU64 < (calldataWord cd 4).toNat := Nat.not_lt.mpr hc.offset
  simp only [decodeSingleDynamic?, Nat.not_lt.mpr hc.head, Nat.not_le.mpr hc.size,
    false_or, if_false, hoff, hv, bind, Option.bind, he]

theorem uintArrayCalldata_bad {cd : ByteArray} (hc : ¬ WordArrayCalldataChecks cd) :
    decodeSingleDynamic? (.dynamicArray abiUInt256) cd = none := by
  cases hd : decodeSingleDynamic? (.dynamicArray abiUInt256) cd with
  | none => rfl
  | some value =>
      obtain ⟨_, _, _, hchecks, _, _⟩ := elemArrayCalldata_facts hd
      exact False.elim (hc hchecks)

theorem decodeCalldataUintArray {cd : ByteArray} (name : Ident)
    (hc : WordArrayCalldataChecks cd) :
    decodeCalldata [name] [.dynamicArray abiUInt256] cd =
      some ((∅ : Store).insert name (.array (calldataUintArrayValues cd))) := by
  rw [decodeCalldata_single_dynamic _ _ _ rfl, uintArrayCalldata_ok hc]
  rfl

theorem decodeCalldataUintArrayBad {cd : ByteArray} (name : Ident)
    (hc : ¬ WordArrayCalldataChecks cd) :
    decodeCalldata [name] [.dynamicArray abiUInt256] cd = none := by
  rw [decodeCalldata_single_dynamic _ _ _ rfl, uintArrayCalldata_bad hc]
  rfl

end Benchmarks.Morpho.MetaMorphoV1_1
