import Benchmarks.Midnight.MulticallTailDecode

/-! Lists and ABI decoding for the direct bytes array passed to multicall. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def multicallBytesList (bytes : ByteArray) (base : UInt256) : Nat → Nat → List ByteArray
  | _, 0 => []
  | start, n + 1 => multicallBytesAt bytes base start :: multicallBytesList bytes base (start + 1) n

def MulticallTailsValid (bytes : ByteArray) (base : UInt256) (start count : Nat) : Prop :=
  ∀ i < count, MulticallTailValid bytes base (start + i)

instance (bytes : ByteArray) (base : UInt256) (start count : Nat) :
    Decidable (MulticallTailsValid bytes base start count) := by
  unfold MulticallTailsValid
  infer_instance

def decodeMulticallTails (bytes : ByteArray) (base : UInt256) (start count : Nat) :
    Option (List ByteArray) :=
  if MulticallTailsValid bytes base start count then
    some (multicallBytesList bytes base start count) else none

theorem multicallBytesList_length (bytes : ByteArray) (base : UInt256) (start count : Nat) :
    (multicallBytesList bytes base start count).length = count := by
  induction count generalizing start with
  | zero => rfl
  | succ count ih => simp only [multicallBytesList, List.length_cons, ih]

theorem multicallBytesList_get (bytes : ByteArray) (base : UInt256) (start count : Nat)
    (i : Nat) (hi : i < count) :
    (multicallBytesList bytes base start count)[i]'(by rw [multicallBytesList_length]; exact hi) =
      multicallBytesAt bytes base (start + i) := by
  induction count generalizing start i with
  | zero => omega
  | succ count ih =>
    cases i with
    | zero => simp only [multicallBytesList, List.getElem_cons_zero, Nat.add_zero]
    | succ i =>
      simpa only [multicallBytesList, List.getElem_cons_succ, Nat.add_assoc, Nat.add_comm 1 i]
        using ih (start + 1) i (by omega)

theorem multicallTailsValid_succ (bytes : ByteArray) (base : UInt256) (start count : Nat) :
    MulticallTailsValid bytes base start (count + 1) ↔
      MulticallTailValid bytes base start ∧ MulticallTailsValid bytes base (start + 1) count := by
  constructor
  · intro h
    refine ⟨by simpa only [Nat.add_zero] using h 0 (by omega), ?_⟩
    intro i hi
    simpa only [Nat.add_assoc, Nat.add_comm 1 i] using h (i + 1) (by omega)
  · rintro ⟨hfirst, hrest⟩ i hi
    cases i with
    | zero => simpa only [Nat.add_zero] using hfirst
    | succ i => simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hrest i (by omega)

theorem decodeMulticallTails_succ (bytes : ByteArray) (base : UInt256) (start count : Nat) :
    decodeMulticallTails bytes base start (count + 1) = (do
      let head ← decodeMulticallTail bytes base start
      let rest ← decodeMulticallTails bytes base (start + 1) count
      pure (head :: rest)) := by
  unfold decodeMulticallTails decodeMulticallTail
  simp only [multicallTailsValid_succ]
  by_cases hh : MulticallTailValid bytes base start <;>
    by_cases ht : MulticallTailsValid bytes base (start + 1) count <;>
    simp only [hh, ht, and_self, and_false, false_and, if_true, if_false,
      bind, Option.bind, pure, multicallBytesList]

theorem solcMulticallElements {bytes : ByteArray} {base : UInt256} {start count : Nat}
    (hs : bytes.size < 2^255) (hb : base.toNat + 32 * (start + count) ≤ bytes.size) :
    decodeElements? .bytes count bytes.toList base.toNat (32 * start)
      { materialize := [] } true =
      (decodeMulticallTails bytes base start count).map (List.map Value.bytes) := by
  induction count generalizing start with
  | zero => simp [decodeElements?, decodeMulticallTails, MulticallTailsValid, multicallBytesList]
  | succ count ih =>
    rw [decodeElements?, decodeMulticallTails_succ]
    simp only [stride?, isDynamicABIType, if_true, bind, Option.bind,
      show child { materialize := [] } .element = { materialize := [] } from rfl,
      show isMemory { materialize := [] } = false from rfl, Bool.not_false, Bool.and_self,
      show (ABIType.bytes == .elem .bool) = false from rfl, Bool.and_false,
      Bool.false_eq_true, if_false, retainFailure,
      show ({ materialize := [] } : CalldataPlan).deferErrors.contains [] = false from rfl]
    have ht := solcDecodeMulticallTail (base := base) (index := start) hs (by omega :
      base.toNat + 32 * start + 32 ≤ bytes.size)
    simp only [bind, Option.bind] at ht
    rw [ht]
    rw [show 32 * start + 32 = 32 * (start + 1) by omega, ih (by omega)]
    cases decodeMulticallTail bytes base start <;>
      cases decodeMulticallTails bytes base (start + 1) count <;> rfl

end Benchmarks.Midnight
