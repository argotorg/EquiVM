import Benchmarks.Midnight.ScalarArrayCalldata
import Benchmarks.Midnight.WordArray

/-! Word lists represented by scalar calldata arrays. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def calldataArrayWords (bytes : ByteArray) : Nat → Nat → List UInt256
  | 0, _ => []
  | n + 1, start => calldataWord bytes start :: calldataArrayWords bytes n (start + 32)

theorem calldataArrayWords_length (bytes : ByteArray) (n start : Nat) :
    (calldataArrayWords bytes n start).length = n := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih => simp only [calldataArrayWords, List.length_cons, ih]

theorem calldataArrayWords_get (bytes : ByteArray) (n start : Nat)
    (i : Fin (calldataArrayWords bytes n start).length) :
    (calldataArrayWords bytes n start)[i] = calldataWord bytes (start + 32 * i.val) := by
  induction n generalizing start with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => simp [calldataArrayWords]
    | succ i =>
      simpa only [calldataArrayWords, List.getElem_cons_succ, Nat.mul_add, Nat.mul_one,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih (start + 32) ⟨i, by
          simp only [calldataArrayWords, List.length_cons] at hi
          omega⟩

def addressWordArrayValues (words : List UInt256) : List Value :=
  words.map (fun w ↦ .address (AccountAddress.ofNat w.toNat))

def CanonicalAddressWords (words : List UInt256) : Prop :=
  ∀ w ∈ words, w.toNat < EVM.addressModulus

instance (words : List UInt256) : Decidable (CanonicalAddressWords words) :=
  inferInstanceAs (Decidable (∀ w ∈ words, w.toNat < EVM.addressModulus))

theorem decodeCalldataWordElements_u256 (bytes : ByteArray) (n start : Nat) :
    decodeCalldataWordElements Model.u256 n bytes start =
      some (wordArrayValues (calldataArrayWords bytes n start)) := by
  induction n generalizing start with
  | zero => rfl
  | succ n ih =>
    simp only [decodeCalldataWordElements, decodeABIWord_u256, bind, Option.bind, ih]
    rfl

theorem decodeCalldataWordElements_address (bytes : ByteArray) (n start : Nat) :
    decodeCalldataWordElements Model.addr n bytes start =
      if CanonicalAddressWords (calldataArrayWords bytes n start) then
        some (addressWordArrayValues (calldataArrayWords bytes n start)) else none := by
  induction n generalizing start with
  | zero => simp [decodeCalldataWordElements, calldataArrayWords,
      CanonicalAddressWords, addressWordArrayValues]
  | succ n ih =>
    rw [decodeCalldataWordElements, decodeABIWord_address]
    by_cases hc : (calldataWord bytes start).toNat < EVM.addressModulus
    · simp only [hc, if_true, bind, Option.bind, ih]
      by_cases hr : CanonicalAddressWords (calldataArrayWords bytes n (start + 32))
      · have hall : CanonicalAddressWords (calldataArrayWords bytes (n + 1) start) := by
          simpa only [CanonicalAddressWords, calldataArrayWords, List.forall_mem_cons] using ⟨hc, hr⟩
        rw [if_pos hall]
        simp only [hr, if_true, calldataArrayWords, addressWordArrayValues, List.map_cons]
        rfl
      · have hall : ¬ CanonicalAddressWords (calldataArrayWords bytes (n + 1) start) := by
          intro h
          exact hr (fun w hw ↦ h w (List.mem_cons_of_mem _ hw))
        simp only [hr, hall, if_false]
    · have hall : ¬ CanonicalAddressWords (calldataArrayWords bytes (n + 1) start) := by
        intro h
        exact hc (h _ List.mem_cons_self)
      simp only [hc, hall, if_false]
      rfl

end Benchmarks.Midnight
