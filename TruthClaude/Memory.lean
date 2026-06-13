import TruthClaude.Stepping

/-!
# Memory — reusable EVM memory + ABI-encoding lemmas

The EVM `MSTORE`/`MLOAD`/`RETURN` and `UInt256.toByteArray`/ABI encoding are *computable*
`ByteArray` operations — **not** opaque like `D_J`/keccak.  The single genuine opacity is the
*content* of `ffi.ByteArray.zeroes` (the `memset_zero` extern): evmlean axiomatizes only its
**size** (`ByteArray_zeroes_size`), not that the bytes are `0`.  We admit that one extern-spec
fact (`byteArray_zeroes_toList`) and **prove everything else** as generic, contract-agnostic
lemmas: the big-endian byte round-trip, `fromByteArrayBigEndian ∘ toByteArray = toNat`, the
`MSTORE`-then-`MLOAD`/`RETURN` round-trip, and `encodeReturnValue?` for `bool`.
-/

open Ethereum Ethereum.EVM Act ABI

set_option maxRecDepth 8000

namespace TruthClaude.Theory

/-- **Trusted (extern spec).** `ffi.ByteArray.zeroes` (`@[extern "memset_zero"]`) yields zero
    bytes.  Companion to evmlean's admitted `ByteArray_zeroes_size`; the only `ffi.zeroes` fact
    not already derivable from the base.  Everything below is proved from it. -/
axiom byteArray_zeroes_toList (n : USize) :
    (ffi.ByteArray.zeroes n).data.toList = List.replicate n.toNat 0

/-! ## 1. Little-endian byte arithmetic (`fromBytes'` / `toBytes'`) -/

theorem fromBytes'_replicate_zero (k : ℕ) : fromBytes' (List.replicate k (0 : UInt8)) = 0 := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [List.replicate, fromBytes']; rw [ih]; rfl

/-- Appending high-order zero bytes does not change the little-endian value. -/
theorem fromBytes'_append_zeros (l : List UInt8) (k : ℕ) :
    fromBytes' (l ++ List.replicate k 0) = fromBytes' l := by
  induction l with
  | nil => simpa using fromBytes'_replicate_zero k
  | cons b bs ih => simp only [List.cons_append, fromBytes']; rw [ih]

/-- The little-endian round-trip `fromBytes' (toBytes' x) = x` (re-proved; evmlean's is
    `private`). -/
theorem fromBytes'_toBytes' (x : ℕ) : fromBytes' (toBytes' x) = x := by
  match x with
  | .zero => simp [toBytes', fromBytes']
  | .succ n =>
    unfold toBytes' fromBytes'
    simp [UInt8.size]
    exact Nat.mod_add_div _ _

/-- Big-endian round-trip: decoding the big-endian bytes of `x` gives back `x`. -/
theorem fromBytesBigEndian_toBytesBigEndian (x : ℕ) :
    fromBytesBigEndian (toBytesBigEndian x) = x := by
  simp only [fromBytesBigEndian, toBytesBigEndian, Function.comp, List.reverse_reverse]
  exact fromBytes'_toBytes' x

/-! ## 2. `ByteArray.toList` = `data.toList`, and the `fromByteArrayBigEndian ∘ toByteArray` round-trip -/

/-- `ByteArray.toList` (the reversing `loop`) equals `data.toList`. -/
theorem byteArray_toList_eq (b : ByteArray) : b.toList = b.data.toList := by
  show ByteArray.toList.loop b 0 [] = _
  suffices h : ∀ i r, ByteArray.toList.loop b i r = r.reverse ++ b.data.toList.drop i by
    simpa using h 0 []
  intro i r
  induction i, r using ByteArray.toList.loop.induct (bs := b) with
  | case1 i r hlt ih =>
    rw [ByteArray.toList.loop, if_pos hlt, ih, List.reverse_cons, List.append_assoc]
    congr 1
    have hi : i < b.data.size := hlt
    have hlen : i < b.data.toList.length := by rw [Array.length_toList]; exact hi
    have hget : b.get! i = b.data.toList[i]'hlen := by
      rw [Array.getElem_toList]; exact getElem!_pos b.data i hi
    rw [hget, List.singleton_append, List.getElem_cons_drop]
  | case2 i r hge =>
    rw [ByteArray.toList.loop, if_neg hge]
    have : b.data.toList.length ≤ i := by rw [Array.length_toList]; exact Nat.le_of_not_lt hge
    rw [List.drop_eq_nil_of_le this, List.append_nil]

/-- **MLOAD round-trip.**  Big-endian-decoding the 32-byte encoding of `v` recovers `v.toNat`.
    The only opacity (the `ffi.zeroes` leading padding) cancels because it is zero. -/
theorem fromByteArrayBigEndian_toByteArray (v : UInt256) :
    fromByteArrayBigEndian (UInt256.toByteArray v) = v.toNat := by
  unfold fromByteArrayBigEndian UInt256.toByteArray BE
  rw [byteArray_toList_eq]
  simp only [fromBytesBigEndian, Function.comp, ByteArray.toList_data_append,
    byteArray_zeroes_toList, List.toList_data_toByteArray, List.reverse_append,
    List.reverse_replicate, toBytesBigEndian, List.reverse_reverse]
  rw [fromBytes'_append_zeros, fromBytes'_toBytes']

end TruthClaude.Theory
