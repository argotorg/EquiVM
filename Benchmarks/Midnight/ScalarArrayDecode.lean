import Benchmarks.Midnight.CollateralDecodeSlice

/-! Decoding scalar calldata arrays one canonical word at a time. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
open ABI.Solc08Calldata

namespace Benchmarks.Midnight

def decodeCalldataWordElements (ty : ABIType) : Nat → ByteArray → Nat → Option (List Value)
  | 0, _, _ => some []
  | n + 1, bytes, start => do
      let value ← decodeABIWord? ty (calldataWord bytes start)
      let rest ← decodeCalldataWordElements ty n bytes (start + 32)
      pure (value :: rest)

theorem decodeCalldataWordElements_eq {ty : ABIType} (hty : isABIScalarWordType ty = true)
    {n : Nat} {bytes : ByteArray} {start : Nat} (hbound : start + 32 * n ≤ bytes.size) :
    decodeABIArrayStaticElems? ty n 32 bytes.toList start =
      (decodeCalldataWordElements ty n bytes start).map
        (fun values ↦ (values, start + 32 * n)) := by
  induction n generalizing start with
  | zero => simp [decodeABIArrayStaticElems?, decodeCalldataWordElements]
  | succ n ih =>
    rw [decodeABIArrayStaticElems?, decodeABIValue_word hty (by omega)]
    cases hd : decodeABIWord? ty (calldataWord bytes start) with
    | none => simp [decodeCalldataWordElements, hd]
    | some value =>
      simp only [Option.map, bind, Option.bind, if_true, ih (start := start + 32) (by omega)]
      simp only [decodeCalldataWordElements, hd, bind, Option.bind]
      cases decodeCalldataWordElements ty n bytes (start + 32) <;> simp only [Option.map]
      congr 2
      omega

theorem decodeCalldataWordElements_extract {ty : ABIType} {bytes : ByteArray}
    {start finish off n : Nat} (hbound : start + off + 32 * n ≤ finish)
    (hfinish : finish ≤ bytes.size) :
    decodeCalldataWordElements ty n (bytes.extract start finish) off =
      decodeCalldataWordElements ty n bytes (start + off) := by
  induction n generalizing off with
  | zero => rfl
  | succ n ih =>
    rw [decodeCalldataWordElements, decodeCalldataWordElements,
      calldataWord_extract (by omega) hfinish, ih (by omega), Nat.add_assoc]

theorem decodeCalldataWords {ty : ABIType} (hty : isABIScalarWordType ty = true)
    {bytes : ByteArray} {start n : Nat}
    (hbound : start + 32 * n ≤ bytes.size) (hsize : bytes.size < EVM.wordModulus) :
    decodeABIArrayStaticElems? ty n 32 (solcReadWords bytes.toList start n) 0 =
      (decodeCalldataWordElements ty n bytes start).map (fun values ↦ (values, 32 * n)) := by
  have hl : bytes.toList.length = bytes.size := by
    simp only [byteArray_toList_eq, Array.length_toList]; rfl
  rw [solcReadWords_bounded (by rw [hl]; exact hbound) (by rw [hl]; exact hsize)]
  have he : (bytes.toList.drop start).take (32 * n) =
      (bytes.extract start (start + 32 * n)).toList := by
    rw [extract_toList]
    congr 1
    omega
  rw [he, decodeCalldataWordElements_eq hty (by rw [ByteArray.size_extract]; omega),
    decodeCalldataWordElements_extract (by omega) hbound]
  simp only [Nat.add_zero, Nat.zero_add]

theorem decodeCalldataWordElements_length {ty : ABIType} {n start : Nat} {bytes : ByteArray}
    {values : List Value} (h : decodeCalldataWordElements ty n bytes start = some values) :
    values.length = n := by
  induction n generalizing start values with
  | zero => simpa [decodeCalldataWordElements] using h.symm
  | succ n ih =>
    simp only [decodeCalldataWordElements, bind, Option.bind] at h
    rcases Option.bind_eq_some_iff.mp h with ⟨value, _, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨rest, hr, he⟩
    cases he
    simp only [List.length_cons, ih hr]

theorem decodeCalldataWordElements_get {ty : ABIType} {n start : Nat} {bytes : ByteArray}
    {values : List Value} (h : decodeCalldataWordElements ty n bytes start = some values)
    (i : Fin values.length) :
    decodeABIWord? ty (calldataWord bytes (start + 32 * i.val)) = some values[i] := by
  induction n generalizing start values with
  | zero =>
    have := decodeCalldataWordElements_length h
    exact False.elim (by have := i.isLt; omega)
  | succ n ih =>
    simp only [decodeCalldataWordElements, bind, Option.bind] at h
    rcases Option.bind_eq_some_iff.mp h with ⟨value, hv, h⟩
    rcases Option.bind_eq_some_iff.mp h with ⟨rest, hr, he⟩
    cases he
    rcases i with ⟨i, hi⟩
    cases i with
    | zero => simpa using hv
    | succ i =>
      simpa only [Nat.mul_add, Nat.mul_one, List.getElem_cons_succ,
        Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
        ih hr ⟨i, by simpa using hi⟩

end Benchmarks.Midnight
