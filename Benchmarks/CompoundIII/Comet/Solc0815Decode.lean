import Reasoning.ABI
import Reasoning.SolmBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE (Reasoning/ABI): the solc 0.8.15 calldata address-array view.
theorem solc0815_addressArrayWord_canonical {n : Nat} (hn : n < EVM.addressModulus) :
    Solc0815.addressArrayWord n = .address (AccountAddress.ofNat n) := by
  simp [Solc0815.addressArrayWord, hn]

theorem solc0815_addressArrayWord_access (n : Nat) :
    normalizeRawBoolWord? (Solc0815.addressArrayWord n) =
      if n < EVM.addressModulus then .ok (.address (AccountAddress.ofNat n)) else .revert := by
  by_cases hn : n < EVM.addressModulus
  · simp [Solc0815.addressArrayWord, hn, normalizeRawBoolWord?]
  · have hn0 : n ≠ 0 := by change ¬ n < 2^160 at hn; omega
    have hn1 : n ≠ 1 := by change ¬ n < 2^160 at hn; omega
    simp [Solc0815.addressArrayWord, hn, rawBoolWordValue, normalizeRawBoolWord?, hn0, hn1]

theorem solc0815_decodeAddressArrayElems_exists {n : Nat} {bytes : List UInt8} {start : Nat}
    (h : start + 32 * n ≤ bytes.length) :
    ∃ values, Solc0815.decodeAddressArrayElems? n bytes start =
      some (values, start + 32 * n) ∧ values.length = n := by
  induction n generalizing start with
  | zero => exact ⟨[], rfl, rfl⟩
  | succ n ih =>
      obtain ⟨word, hword⟩ := readNat?_exists_of_length (bytes := bytes) (off := start) (by omega)
      obtain ⟨values, hvalues, hlen⟩ := ih (start := start + 32) (by omega)
      refine ⟨Solc0815.addressArrayWord word :: values, ?_, by simp [hlen]⟩
      simp [Solc0815.decodeAddressArrayElems?, hword, hvalues, Nat.mul_add, Nat.add_assoc,
        Nat.add_comm]

theorem solc0815_decodeAddressArrayElems_facts {n : Nat} {bytes : List UInt8} {start : Nat}
    {values : List Value} {endOffset : Nat} (hstart : start ≤ bytes.length)
    (h : Solc0815.decodeAddressArrayElems? n bytes start = some (values, endOffset)) :
    endOffset = start + 32 * n ∧ endOffset ≤ bytes.length ∧ values.length = n := by
  induction n generalizing start values endOffset with
  | zero =>
      simp [Solc0815.decodeAddressArrayElems?] at h
      rcases h with ⟨rfl, rfl⟩
      exact ⟨by omega, hstart, rfl⟩
  | succ n ih =>
      rw [Solc0815.decodeAddressArrayElems?] at h
      cases hword : readNat? bytes start with
      | none => simp [hword] at h
      | some word =>
          have hlen := readNat?_some_length hword
          cases hrest : Solc0815.decodeAddressArrayElems? n bytes (start + 32) with
          | none => simp [hword, hrest] at h
          | some rest =>
              rcases rest with ⟨tail, tailEnd⟩
              simp [hword, hrest] at h
              rcases h with ⟨rfl, rfl⟩
              obtain ⟨hend, hle, hlength⟩ := ih hlen hrest
              exact ⟨by omega, hle, by simp [hlength]⟩

theorem solc0815_decodeAddressArrayElems_getElem {n : Nat} {bytes : List UInt8} {start : Nat}
    {values : List Value} {endOffset i : Nat}
    (h : Solc0815.decodeAddressArrayElems? n bytes start = some (values, endOffset))
    (hi : i < n) :
    ∃ word, readNat? bytes (start + 32 * i) = some word ∧
      values[i]? = some (Solc0815.addressArrayWord word) := by
  induction n generalizing start values endOffset i with
  | zero => omega
  | succ n ih =>
      rw [Solc0815.decodeAddressArrayElems?] at h
      cases hword : readNat? bytes start with
      | none => simp [hword] at h
      | some word =>
          cases hrest : Solc0815.decodeAddressArrayElems? n bytes (start + 32) with
          | none => simp [hword, hrest] at h
          | some rest =>
              rcases rest with ⟨tail, tailEnd⟩
              simp [hword, hrest] at h
              rcases h with ⟨rfl, rfl⟩
              cases i with
              | zero => exact ⟨word, by simpa using hword, rfl⟩
              | succ i =>
                  obtain ⟨word', hread, hget⟩ := ih hrest (by omega : i < n)
                  refine ⟨word', ?_, hget⟩
                  convert hread using 1
                  congr 1
                  omega

-- LIBRARY CANDIDATE (Reasoning/SolmBody): connect the evaluator's lookup to list indexing.
theorem lookupNth_eq_getElem? {α : Type} (values : List α) (i : Nat) :
    lookupNth? values i = values[i]? := by
  induction values generalizing i with
  | nil => simp [lookupNth?]
  | cons value values ih => cases i <;> simp [lookupNth?, ih]

theorem solc0815_decodeAddressArrayElems_index {n : Nat} {bytes : List UInt8} {start : Nat}
    {values : List Value} {endOffset i : Nat}
    (h : Solc0815.decodeAddressArrayElems? n bytes start = some (values, endOffset))
    (hlen : values.length = n) (hi : i < n) :
    ∃ word, readNat? bytes (start + 32 * i) = some word ∧
      evalIndex? (.array values) (.int (Int.ofNat i)) =
        if word < EVM.addressModulus then .ok (.address (AccountAddress.ofNat word))
        else .revert := by
  obtain ⟨word, hread, hget⟩ := solc0815_decodeAddressArrayElems_getElem h hi
  refine ⟨word, hread, ?_⟩
  have hilt : (i : Int) < values.length := by exact_mod_cast (hlen ▸ hi)
  change evalIndex? (.array values) (.int (i : Int)) = _
  simp only [evalIndex?, Int.natCast_nonneg, hilt, and_self, if_true, Int.toNat_natCast,
    lookupNth_eq_getElem?, hget]
  exact solc0815_addressArrayWord_access word

theorem solc0815_decodeAddressArray_ok {bytes : List UInt8} {start n : Nat}
    {values : List Value} {endOffset : Nat}
    (hread : readNat? bytes start = some n) (hn : n ≤ solcMaxU64)
    (h : Solc0815.decodeAddressArrayElems? n bytes (start + 32) = some (values, endOffset)) :
    decodeABIValue? (.dynamicArray (.elem .address)) bytes start .solc0815 =
      some (.array values, endOffset) := by
  simp [decodeABIValue?, hread, solcMaxLen, Nat.not_lt.mpr hn, h]

end Benchmarks.CompoundIII.Comet
