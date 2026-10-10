import Benchmarks.UniswapV4PoolManager.DynamicDecode
import Reasoning.ABIViews

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 1000

theorem decodeCalldata_singleArray_eq (cd : ByteArray) (elem : ABIType) (name : Ident) :
    decodeCalldata [name] [.dynamicArray elem] cd =
      if cd.size < 36 ∨ 2 ^ 255 ≤ cd.size then none
      else if solcMaxU64 < (calldataWord cd 4).toNat then none
      else (decodeABIValue? (.dynamicArray elem) (cd.toList.drop 4)
        (calldataWord cd 4).toNat).map (fun p ↦ (∅ : Store).insert name p.1) :=
  decodeCalldata_singleDynamic_eq cd (.dynamicArray elem) name rfl

-- LIBRARY CANDIDATE: decoding a bytes32 array is equivalent to the compiler's head bounds.
def WordArrayBounds (cd : ByteArray) : Prop :=
  36 ≤ cd.size ∧ cd.size < 2 ^ 255 ∧ (calldataWord cd 4).toNat ≤ solcMaxU64 ∧
  4 + (calldataWord cd 4).toNat + 32 ≤ cd.size ∧
  (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤ solcMaxU64 ∧
  4 + (calldataWord cd 4).toNat + 32 +
    32 * (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat ≤ cd.size

structure WordArrayDecoded (cd : ByteArray) (values : List Value) : Prop where
  bounds : WordArrayBounds cd
  decode : decodeABIValue? (.dynamicArray abiBytes32) (cd.toList.drop 4)
    (calldataWord cd 4).toNat = some (.array values,
      (calldataWord cd 4).toNat + 32 + 32 * values.length)
  length : values.length = (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat

theorem decodeCalldata_wordArray_some {cd : ByteArray} {name : Ident} {args : Store}
    (h : decodeCalldata [name] [.dynamicArray abiBytes32] cd = some args) :
    ∃ values, args = (∅ : Store).insert name (.array values) ∧ WordArrayDecoded cd values := by
  rw [decodeCalldata_singleArray_eq] at h
  split at h
  · contradiction
  rename_i hs
  split at h
  · contradiction
  rename_i ho
  cases hv : decodeABIValue? (.dynamicArray abiBytes32) (cd.toList.drop 4)
      (calldataWord cd 4).toNat with
  | none => simp only [hv, Option.map_none] at h; cases h
  | some p =>
      obtain ⟨values, hvalues⟩ := decodeABIValue_dynamicArray_is_array hv
      rcases p with ⟨value, endOffset⟩
      dsimp only at hvalues
      subst value
      have htlen : (cd.toList.drop 4).length = cd.size - 4 := by
        rw [List.length_drop, byteArray_toList_eq, Array.length_toList]; rfl
      obtain ⟨len, hr, hm, he, hb, hl⟩ := decodeABIValue_dynamicArray_elem32_facts hv
      have hhead := readNat?_some_length hr
      rw [htlen] at hhead hb
      have hr' := readNat_drop4_dynamic_eq_calldataWord (cd := cd) (by omega)
      rw [hr'] at hr
      have hlen : len = (calldataWord cd (4 + (calldataWord cd 4).toNat)).toNat :=
        (Option.some.inj hr).symm
      refine ⟨values, ?_, ⟨?_, ?_, by omega⟩⟩
      · simpa only [hv, Option.map_some, Option.some.injEq] using h.symm
      · unfold WordArrayBounds
        omega
      · rw [← hl] at he
        simpa only [he] using hv

theorem decodeCalldata_wordArray_exists {cd : ByteArray} (name : Ident)
    (hb : WordArrayBounds cd) :
    ∃ values, WordArrayDecoded cd values ∧
      decodeCalldata [name] [.dynamicArray abiBytes32] cd =
        some ((∅ : Store).insert name (.array values)) := by
  rcases hb with ⟨hs, hh, ho, hr, hn, hp⟩
  have htlen : (cd.toList.drop 4).length = cd.size - 4 := by
    rw [List.length_drop, byteArray_toList_eq, Array.length_toList]; rfl
  obtain ⟨values, hv, hl⟩ := decodeABIValue_dynamicArray_bytes32_exists
    (readNat_drop4_dynamic_eq_calldataWord hr) (by omega) (by rw [htlen]; omega)
  refine ⟨values, ⟨⟨hs, hh, ho, hr, hn, hp⟩, by simpa only [hl] using hv, hl⟩, ?_⟩
  rw [decodeCalldata_singleArray_eq, if_neg (by omega), if_neg (by omega), hv]
  rfl

theorem decodeCalldata_wordArray_none {cd : ByteArray} (name : Ident)
    (hb : ¬ WordArrayBounds cd) :
    decodeCalldata [name] [.dynamicArray abiBytes32] cd = none := by
  cases hd : decodeCalldata [name] [.dynamicArray abiBytes32] cd with
  | none => rfl
  | some args =>
      obtain ⟨_, _, h⟩ := decodeCalldata_wordArray_some hd
      exact (hb h.bounds).elim

-- The decoded source lookup and CALLDATALOAD select the same word, including unaligned heads.
theorem WordArrayDecoded.lookup {I : ExecutionEnv} {values : List Value}
    (h : WordArrayDecoded I.calldata values) {i : Nat} (hi : i < values.length) :
    lookupNth? values i = some (.fixedBytes abiBytes32Width (EVM.Word.toBytesBE
      (calldataWord I.calldata (4 + (calldataWord I.calldata 4).toNat + 32 + 32 * i)))) := by
  obtain ⟨word, hw⟩ := decodeABIValue_dynamicArray_bytes32_lookup_shape h.decode hi
  have hr := decodeABIValue_dynamicArray_bytes32_lookup_readNat h.decode hw
  have hb := h.bounds.2.2.2.2.2
  rw [← h.length] at hb
  have hr' := readNat_drop4_eq_calldataWord (I := I)
    (headOff := (calldataWord I.calldata 4).toNat + 32 + 32 * i) (by omega)
  rw [hr'] at hr
  have he : word = calldataWord I.calldata
      (4 + (calldataWord I.calldata 4).toNat + 32 + 32 * i) := by
    apply u256_inj
    simpa only [UInt256.toNat, Nat.add_assoc] using (Option.some.inj hr).symm
  simpa only [he] using hw

end Benchmarks.UniswapV4PoolManager
