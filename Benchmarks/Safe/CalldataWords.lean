import Benchmarks.Safe.DynamicCalldata
import Benchmarks.Safe.WordArrayMemory
import Benchmarks.Safe.LocalArrays

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a finite sequence of consecutive CALLDATALOAD values.
def calldataWords (cd : ByteArray) (off : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => calldataWord cd off :: calldataWords cd (off + 32) n

theorem calldataWords_length (cd : ByteArray) (off n : Nat) :
    (calldataWords cd off n).length = n := by
  induction n generalizing off <;> simp [calldataWords, *]

theorem calldataWords_get (cd : ByteArray) (off n i : Nat) (hi : i < n) :
    (calldataWords cd off n)[i]'(by rw [calldataWords_length]; exact hi) =
      calldataWord cd (off + 32 * i) := by
  induction n generalizing off i with
  | zero => omega
  | succ n ih =>
      cases i with
      | zero => simp [calldataWords]
      | succ i =>
          simpa [calldataWords, Nat.mul_add, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
            ih (off + 32) i (by omega)

theorem calldataWords_view (cd : ByteArray) (off n : Nat) (hin : off + 32 * n ≤ cd.size) :
    WordArrayMemory cd off (calldataWords cd off n) := by
  intro i hi
  have hi' : i < n := by rwa [calldataWords_length] at hi
  rw [calldataWords_get cd off n i hi', calldataWord_bytes_at (by omega),
    readWithPadding_eq_extract_unbounded _ _ 32 (by decide) (by omega)]

-- LIBRARY CANDIDATE: scalar address-array decoding validates each loaded word.
theorem decodeAddressArrayElements {cd : ByteArray} (off n : Nat)
    (hin : 4 + off + 32 * n ≤ cd.size) :
    decodeABIArrayStaticElems? (.elem .address) n 32 (cd.toList.drop 4) off =
      if ∀ w ∈ calldataWords cd (4 + off) n, w.toNat < EVM.addressModulus then
        some ((calldataWords cd (4 + off) n).map addressArrayValue, off + 32 * n)
      else none := by
  induction n generalizing off with
  | zero => simp [decodeABIArrayStaticElems?, calldataWords]
  | succ n ih =>
      rw [decodeABIArrayStaticElems?, decodeAddressCalldata off (by omega)]
      by_cases hc : (calldataWord cd (4 + off)).toNat < EVM.addressModulus
      · rw [if_pos hc]
        dsimp only [bind, Option.bind]
        rw [if_pos rfl, ih (off + 32) (by omega)]
        by_cases ht : ∀ w ∈ calldataWords cd (4 + off + 32) n, w.toNat < EVM.addressModulus
        all_goals
          simp only [calldataWords, List.mem_cons, forall_eq_or_imp, hc, true_and,
            ← Nat.add_assoc, ht, ↓reduceIte, bind, Option.bind, List.map_cons, addressArrayValue]
        rw [if_pos ht, if_pos ht]
        dsimp only
        congr 2
        omega
      · simp [hc, calldataWords, addressArrayValue]

end Benchmarks.Safe
