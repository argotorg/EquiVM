import Benchmarks.Morpho.MetaMorphoV1_1.WordArrayStorage

/-! Store-order identities for complete array replacement. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.Morpho.MetaMorphoV1_1

-- LIBRARY CANDIDATE: writes erase the effect of earlier writes to any covered slot.
theorem storeWordArray_absorbStore (owner : AccountAddress) (base : UInt256)
    (words : Nat → UInt256) (value : UInt256) (n : Nat) :
    ∀ (σ : AccountMap) (index j : Nat), index ≤ j → j < index + n →
      storeWordArray owner (sstoreAccountMap owner σ (base + UInt256.ofNat j) value)
        base words index n = storeWordArray owner σ base words index n := by
  induction n with
  | zero => intro σ index j hlo hhi; omega
  | succ n ih =>
      intro σ index j hlo hhi
      rw [storeWordArray, storeWordArray]
      by_cases he : base + UInt256.ofNat j = base + UInt256.ofNat index
      · rw [he, ← sstoreAccountMap_self_update]
      · rw [sstoreAccountMap_comm _ _ _ _ _ _ he]
        apply ih
        · by_contra h
          have hj : j = index := by omega
          exact he (by rw [hj])
        · omega

-- LIBRARY CANDIDATE: clearing any prefix later overwritten is unobservable.
theorem storeWordArray_absorbClear (owner : AccountAddress) (base : UInt256)
    (words : Nat → UInt256) (index n count : Nat) :
    ∀ (σ : AccountMap) (start : Nat), index ≤ start → start + count ≤ index + n →
      storeWordArray owner
        (clearDataWordsForwardFrom owner σ base (UInt256.ofNat start) count)
        base words index n = storeWordArray owner σ base words index n := by
  induction count with
  | zero => intros; rfl
  | succ count ih =>
      intro σ start hlo hhi
      rw [clearDataWordsForwardFrom, u256_one_add_ofNat]
      rw [ih _ (start + 1) (by omega) (by omega)]
      exact storeWordArray_absorbStore owner base words ⟨0⟩ n σ index start hlo (by omega)

-- LIBRARY CANDIDATE: a separate header write commutes with all data writes.
theorem storeWordArray_store_comm (owner : AccountAddress) (base slot value : UInt256)
    (words : Nat → UInt256) (n : Nat) :
    ∀ (σ : AccountMap) (index : Nat),
      (∀ j, index ≤ j → j < index + n → slot ≠ base + UInt256.ofNat j) →
      storeWordArray owner (sstoreAccountMap owner σ slot value) base words index n =
        sstoreAccountMap owner (storeWordArray owner σ base words index n) slot value := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
      intro σ index hne
      rw [storeWordArray, storeWordArray, sstoreAccountMap_comm _ _ _ _ _ _
        (hne index (by omega) (by omega))]
      exact ih _ (index + 1) (fun j hlo hhi ↦ hne j (by omega) (by omega))

-- LIBRARY CANDIDATE: a full replacement only needs to clear the old suffix.
theorem storeWordArray_clearSuffix (owner : AccountAddress) (base : UInt256)
    (words : Nat → UInt256) (σ : AccountMap) (oldLength n : Nat) :
    storeWordArray owner
      (clearDataWordsForwardFrom owner σ base ⟨0⟩ oldLength) base words 0 n =
    storeWordArray owner
      (clearDataWordsForwardFrom owner σ base (UInt256.ofNat n) (oldLength - n))
      base words 0 n := by
  by_cases h : oldLength ≤ n
  · rw [Nat.sub_eq_zero_of_le h, clearDataWordsForwardFrom]
    exact storeWordArray_absorbClear owner base words 0 n oldLength σ 0 (by omega) (by omega)
  · have he : oldLength = n + (oldLength - n) := by omega
    conv_lhs => rw [he, clearDataWordsForwardFrom_split n (oldLength - n),
      clearDataWordsLoopIndex_zero_ofNat]
    exact storeWordArray_absorbClear owner base words 0 n n _ 0 (by omega) (by omega)

-- LIBRARY CANDIDATE: compiler order for replacing an array after its length store.
def replaceWordArrayRuntimeAccounts (owner : AccountAddress) (σ : AccountMap)
    (header base : UInt256) (oldLength : Nat) (words : Nat → UInt256) (n : Nat) : AccountMap :=
  storeWordArray owner
    (clearDataWordsForwardFrom owner (sstoreAccountMap owner σ header (UInt256.ofNat n))
      (base + UInt256.ofNat n) ⟨0⟩ (oldLength - n)) base words 0 n

-- GENERALIZES Reasoning.Theory.clearDataWordsForwardFrom_shift_ofNat without a count bound.
theorem clearWordArray_shift (owner : AccountAddress) (base offset : UInt256) (n : Nat) :
    ∀ (σ : AccountMap) (i : UInt256),
      clearDataWordsForwardFrom owner σ (base + offset) i n =
        clearDataWordsForwardFrom owner σ base (offset + i) n := by
  induction n with
  | zero => intros; rfl
  | succ n ih =>
      intro σ i
      simp only [clearDataWordsForwardFrom, u256_add_assoc, ih]
      rw [← u256_add_assoc offset ⟨1⟩ i, u256_add_comm offset ⟨1⟩, u256_add_assoc]

-- LIBRARY CANDIDATE: replacement orders agree when the header is outside the data slots.
theorem replaceWordArrayAccounts_match (owner : AccountAddress) (σ : AccountMap)
    (header base : UInt256) (words : Nat → UInt256) (oldLength n : Nat)
    (hold : ∀ j, j < oldLength → header ≠ base + UInt256.ofNat j)
    (hnew : ∀ j, j < n → header ≠ base + UInt256.ofNat j) :
    replaceWordArraySourceAccounts owner σ header base oldLength words n =
      replaceWordArrayRuntimeAccounts owner σ header base oldLength words n := by
  unfold replaceWordArraySourceAccounts replaceWordArrayRuntimeAccounts
  rw [← storeWordArray_store_comm owner _ header (UInt256.ofNat n) words n _ 0
      (fun j _ hj ↦ hnew j (by omega)), ← sstoreAccountMap_self_update]
  rw [← clearDataWordsForwardFrom_sstore_comm owner _ header (UInt256.ofNat n) oldLength σ hold]
  rw [storeWordArray_clearSuffix, clearWordArray_shift, uint256_add_zero_right]

end Benchmarks.Morpho.MetaMorphoV1_1
