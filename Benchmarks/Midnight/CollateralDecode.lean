import Benchmarks.Midnight.CollateralData
import Benchmarks.Midnight.ABIWordDecode

/-! Exact ABI decoding of a collateral tuple, including both address checks. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem collateralABI_headSize :
    abiTupleHeadSize? [Model.addr, Model.u256, Model.u256, Model.addr] = some 128 := by
  simp [abiTupleHeadSize?, Model.addr, Model.u256, isDynamicABIType, staticABIEncodedSize?]

theorem collateralABI_staticSize : staticABIEncodedSize? Model.collateralABI = some 128 := by
  simp [Model.collateralABI, staticABIEncodedSize?, staticABIEncodedSizeList?,
    Model.addr, Model.u256]

theorem decodeCollateral_bound {bytes : ByteArray} {start stop : Nat} {value : Value}
    (h : decodeABIValue? Model.collateralABI bytes.toList start = some (value, stop)) :
    start + 128 ≤ bytes.size := by
  rw [Model.collateralABI, decodeABIValue?, collateralABI_headSize] at h
  simp only [bind, Option.bind] at h
  rcases Option.bind_eq_some_iff.mp h with ⟨⟨values, stop'⟩, hd, _⟩
  have hb := decodeABIWordHeads_bound (by
    simp only [List.forall_mem_cons]
    decide) hd
  rcases hb with hn | hb
  · cases hn
  · simpa only [List.length_cons, List.length_nil, byteArray_toList_eq,
      Array.length_toList, Nat.add_zero, Nat.reduceAdd, Nat.reduceMul] using hb

theorem decodeCollateral_short {bytes : ByteArray} {start : Nat}
    (hshort : bytes.size < start + 128) :
    decodeABIValue? Model.collateralABI bytes.toList start = none := by
  cases hd : decodeABIValue? Model.collateralABI bytes.toList start with
  | none => rfl
  | some pair => have hb := decodeCollateral_bound hd; omega

theorem decodeCollateral_full {bytes : ByteArray} {start : Nat}
    (hlen : start + 128 ≤ bytes.size) :
    decodeABIValue? Model.collateralABI bytes.toList start =
      if CollateralData.canonicalAt bytes start then
        some ((CollateralData.at bytes start).value, start + 128) else none := by
  rw [Model.collateralABI, decodeABIValue?, collateralABI_headSize]
  simp only [bind, Option.bind]
  rw [decodeABIValues_word (by rfl) (by omega)]
  rw [decodeABIWord_address]
  by_cases ht : (calldataWord bytes start).toNat < EVM.addressModulus
  · simp only [Nat.add_zero, ht, if_true, bind, Option.bind]
    rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_u256]
    simp only [bind, Option.bind]
    rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_u256]
    simp only [bind, Option.bind]
    rw [decodeABIValues_word (by rfl) (by omega), decodeABIWord_address]
    simp only [Nat.reduceAdd]
    by_cases ho : (calldataWord bytes (start + 96)).toNat < EVM.addressModulus
    · simp only [ho, if_true, bind, Option.bind, decodeABIValues?]
      simp only [CollateralData.canonicalAt, ht, ho, and_self, if_true,
        CollateralData.at, CollateralData.value, Nat.add_zero]
      congr 2
      omega
    · simp [ho, CollateralData.canonicalAt]
  · simp [ht, CollateralData.canonicalAt]

theorem decodeCollateral {bytes : ByteArray} {start : Nat} :
    decodeABIValue? Model.collateralABI bytes.toList start =
      if start + 128 ≤ bytes.size ∧ CollateralData.canonicalAt bytes start then
        some ((CollateralData.at bytes start).value, start + 128) else none := by
  by_cases hlen : start + 128 ≤ bytes.size
  · rw [decodeCollateral_full hlen]
    simp only [hlen, true_and]
  · rw [decodeCollateral_short (by omega)]
    simp only [hlen, false_and, if_false]

def decodeCollateralElements : Nat → ByteArray → Nat → Option (List CollateralData)
  | 0, _, _ => some []
  | n + 1, bytes, start =>
      if start + 128 ≤ bytes.size ∧ CollateralData.canonicalAt bytes start then
        (decodeCollateralElements n bytes (start + 128)).map (CollateralData.at bytes start :: ·)
      else none

theorem decodeCollateralElements_eq (n : Nat) (bytes : ByteArray) (start : Nat) :
    decodeABIArrayStaticElems? Model.collateralABI n 128 bytes.toList start =
      (decodeCollateralElements n bytes start).map
        (fun values ↦ (values.map CollateralData.value, start + 128 * n)) := by
  induction n generalizing start with
  | zero => simp [decodeABIArrayStaticElems?, decodeCollateralElements]
  | succ n ih =>
    rw [decodeABIArrayStaticElems?, decodeCollateral]
    simp only [decodeCollateralElements]
    split
    · simp only [bind, Option.bind, if_true, ih]
      cases decodeCollateralElements n bytes (start + 128) <;>
        simp only [Option.map, List.map_cons]
      congr 2
      omega
    · rfl

theorem decodeCollateralElements_length {n start : Nat} {bytes : ByteArray}
    {values : List CollateralData} (h : decodeCollateralElements n bytes start = some values) :
    values.length = n := by
  induction n generalizing start values with
  | zero => simpa [decodeCollateralElements] using h.symm
  | succ n ih =>
    rw [decodeCollateralElements] at h
    split at h
    · cases hd : decodeCollateralElements n bytes (start + 128) with
      | none => simp [hd] at h
      | some rest =>
        simp only [hd, Option.map, Option.some.injEq] at h
        subst values
        simp only [List.length_cons, ih hd]
    · cases h

theorem decodeCollateralElements_bound {n start : Nat} {bytes : ByteArray}
    {values : List CollateralData} (h : decodeCollateralElements n bytes start = some values) :
    n = 0 ∨ start + 128 * n ≤ bytes.size := by
  induction n generalizing start values with
  | zero => exact Or.inl rfl
  | succ n ih =>
    right
    rw [decodeCollateralElements] at h
    split at h
    · rename_i hhead
      cases hd : decodeCollateralElements n bytes (start + 128) with
      | none => simp [hd] at h
      | some rest =>
        rcases ih hd with hz | hb
        · subst n; simpa using hhead.1
        · omega
    · cases h

theorem decodeCollateralElements_short {n start : Nat} {bytes : ByteArray}
    (hpos : 0 < n) (hshort : bytes.size < start + 128 * n) :
    decodeCollateralElements n bytes start = none := by
  cases hd : decodeCollateralElements n bytes start with
  | none => rfl
  | some values => have hb := decodeCollateralElements_bound hd; omega

theorem decodeCollateralArray (bytes : ByteArray) (start : Nat) :
    decodeABIValue? (.dynamicArray Model.collateralABI) bytes.toList start = (do
      let n ← readNat? bytes.toList start
      if solcMaxU64 < n then none else
        let values ← decodeCollateralElements n bytes (start + 32)
        pure (.array (values.map CollateralData.value), start + 32 + 128 * n)) := by
  rw [decodeABIValue?]
  have hd : isDynamicABIType Model.collateralABI = false := rfl
  have hs := collateralABI_staticSize
  simp only [Model.collateralABI] at hd hs ⊢
  simp only [hd, Bool.false_eq_true, if_false, hs, bind, Option.bind, solcMaxLen_modern]
  cases readNat? bytes.toList start with
  | none => rfl
  | some n =>
    by_cases hc : solcMaxU64 < n
    · simp only [hc, if_true]
    · simp only [hc, if_false]
      have he := decodeCollateralElements_eq n bytes (start + 32)
      simp only [Model.collateralABI] at he
      rw [he]
      cases decodeCollateralElements n bytes (start + 32) <;> rfl

end Benchmarks.Midnight
