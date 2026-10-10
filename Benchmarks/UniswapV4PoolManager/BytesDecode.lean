import Benchmarks.UniswapV4PoolManager.DynamicDecode

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: bytes decoding reduces to a bounded length and payload slice.
theorem decodeABIValue_bytes_eq (bytes : List UInt8) (start : Nat) :
    decodeABIValue? .bytes bytes start =
      match readNat? bytes start with
      | none => none
      | some len => if len ≤ solcMaxU64 ∧ start+32+len ≤ bytes.length then
          some (.bytes ⟨((bytes.drop (start+32)).take len).toArray⟩, start+32+paddedSize len) else none := by
  rw [decodeABIValue?]
  cases hr : readNat? bytes start with
  | none => rfl
  | some len =>
    have hh := readNat?_some_length hr
    by_cases hl : len ≤ solcMaxU64
    · have hn : ¬solcMaxU64 < len := by omega
      simp only [bind, Option.bind, solcMaxLen, hn, if_false, hl, true_and, readBytes?]
      by_cases hp : start+32+len ≤ bytes.length
      · rw [if_pos hp, if_pos (by rw [List.length_take, List.length_drop]; omega)]
      · rw [if_neg hp, if_neg (by rw [List.length_take, List.length_drop]; omega)]
    · have hn : solcMaxU64 < len := by omega
      simp only [bind, Option.bind, solcMaxLen, hn, if_true, hl, false_and, if_false]

-- LIBRARY CANDIDATE: dynamic bytes in calldata, including unaligned or aliased offsets.
def BytesSliceBounds (cd : ByteArray) (start : Nat) : Prop :=
  cd.size < 2^255 ∧ start+32 ≤ cd.size ∧ (calldataWord cd start).toNat ≤ solcMaxU64 ∧
  start+32+(calldataWord cd start).toNat ≤ cd.size

def BytesCalldataBounds (cd : ByteArray) : Prop :=
  36 ≤ cd.size ∧ cd.size < 2^255 ∧ (calldataWord cd 4).toNat ≤ solcMaxU64 ∧
  4+(calldataWord cd 4).toNat+32 ≤ cd.size ∧
  (calldataWord cd (4+(calldataWord cd 4).toNat)).toNat ≤ solcMaxU64 ∧
  4+(calldataWord cd 4).toNat+32+(calldataWord cd (4+(calldataWord cd 4).toNat)).toNat ≤ cd.size

def calldataBytesPayload (cd : ByteArray) : ByteArray :=
  cd.extract (4+(calldataWord cd 4).toNat+32)
    (4+(calldataWord cd 4).toNat+32+(calldataWord cd (4+(calldataWord cd 4).toNat)).toNat)

-- LIBRARY CANDIDATE: converting a list slice back to its byte-array representation.
theorem bytesSlice_eq_extract (bytes : ByteArray) (start len : Nat) :
    (⟨((bytes.toList.drop start).take len).toArray⟩ : ByteArray) = bytes.extract start (start+len) := by
  rw [mk_toArray_eq]
  have h := byteArray_toList_toByteArray (bytes.extract start (start+len))
  simpa only [extract_toList, Nat.add_sub_cancel_left] using h

theorem calldataBytesPayload_eq (cd : ByteArray) :
    (⟨(((cd.toList.drop 4).drop ((calldataWord cd 4).toNat+32)).take
      (calldataWord cd (4+(calldataWord cd 4).toNat)).toNat).toArray⟩ : ByteArray) = calldataBytesPayload cd := by
  dsimp only [calldataBytesPayload]
  rw [List.drop_drop]
  simpa only [Nat.add_assoc] using bytesSlice_eq_extract cd (4+(calldataWord cd 4).toNat+32)
    (calldataWord cd (4+(calldataWord cd 4).toNat)).toNat

theorem decodeCalldata_bytes_ok {cd : ByteArray} (name : Ident) (hb : BytesCalldataBounds cd) :
    decodeCalldata [name] [.bytes] cd = some ((∅ : Store).insert name (.bytes (calldataBytesPayload cd))) := by
  rcases hb with ⟨hs, hh, ho, hl, hn, hp⟩
  rw [decodeCalldata_singleDynamic_eq cd .bytes name rfl, if_neg (by omega), if_neg (by omega),
    decodeABIValue_bytes_eq, readNat_drop4_dynamic_eq_calldataWord hl]
  simp only []
  rw [if_pos ⟨hn, by
    rw [List.length_drop, byteArray_toList_eq, Array.length_toList]
    change (calldataWord cd 4).toNat+32+
      (calldataWord cd (4+(calldataWord cd 4).toNat)).toNat ≤ cd.size-4
    omega⟩]
  simp only [Option.map_some, calldataBytesPayload_eq]

theorem decodeCalldata_bytes_bounds {cd : ByteArray} {name : Ident} {args : Store}
    (h : decodeCalldata [name] [.bytes] cd = some args) : BytesCalldataBounds cd := by
  rw [decodeCalldata_singleDynamic_eq cd .bytes name rfl] at h
  split at h
  · contradiction
  rename_i hs
  split at h
  · contradiction
  rename_i ho
  rw [decodeABIValue_bytes_eq] at h
  cases hr : readNat? (cd.toList.drop 4) (calldataWord cd 4).toNat with
  | none => simp only [hr, Option.map_none] at h; cases h
  | some len =>
    have htlen : (cd.toList.drop 4).length = cd.size-4 := by
      rw [List.length_drop, byteArray_toList_eq, Array.length_toList]; rfl
    have hh := readNat?_some_length hr
    rw [htlen] at hh
    have hr' := readNat_drop4_dynamic_eq_calldataWord (cd := cd) (by omega)
    have he : len = (calldataWord cd (4+(calldataWord cd 4).toNat)).toNat :=
      (Option.some.inj (hr.symm.trans hr'))
    rw [hr] at h
    simp only [] at h
    split at h
    · rename_i hb
      rw [htlen, he] at hb
      unfold BytesCalldataBounds
      omega
    · simp only [Option.map_none] at h; cases h

theorem decodeCalldata_bytes_none {cd : ByteArray} (name : Ident) (hb : ¬BytesCalldataBounds cd) :
    decodeCalldata [name] [.bytes] cd = none := by
  cases hd : decodeCalldata [name] [.bytes] cd with
  | none => rfl
  | some args => exact (hb (decodeCalldata_bytes_bounds hd)).elim

end Benchmarks.UniswapV4PoolManager
