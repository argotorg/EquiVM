import Benchmarks.EAS.Attester.AttestCellRead
import Benchmarks.EAS.Attester.AttestArrayEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem attestArrayItemEncodedMemory_read_body (mem : ByteArray) (origin table dst : Nat)
    (input : UInt256) :
    (attestArrayItemEncodedMemory mem origin table dst input).readWithPadding dst 256 =
      wordBytes (attestCellWords input) := attestCellEncodedMemory_read _ _ _

theorem attestArrayItemEncodedMemory_read_table {mem : ByteArray} {origin table dst : Nat}
    {input : UInt256} (ht : table + 32 ≤ dst) :
    (attestArrayItemEncodedMemory mem origin table dst input).readWithPadding table 32 =
      (UInt256.ofNat (dst - origin - 96)).toByteArray := by
  rw [attestArrayItemEncodedMemory, attestCellEncodedMemory_read_below
    (by rw [writeWord_sparse_size]; omega) ht, writeWord_sparse_read_back]

theorem attestArrayItemEncodedMemory_preserves {mem : ByteArray}
    {origin table dst read len : Nat} {input : UInt256}
    (hin : read + len ≤ mem.size) (hbelow : read + len ≤ dst)
    (hdis : read + len ≤ table ∨ table + 32 ≤ read) :
    (attestArrayItemEncodedMemory mem origin table dst input).readWithPadding read len =
      mem.readWithPadding read len := by
  rw [attestArrayItemEncodedMemory, attestCellEncodedMemory_read_below
    (by rw [writeWord_sparse_size]; omega) hbelow]
  exact writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin hdis

def attestArrayTailWords (values : Nat → UInt256) (i : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => attestCellWords (values i) ++ attestArrayTailWords values (i + 1) n

def attestArrayOffsetWords (origin dst : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => UInt256.ofNat (dst - origin - 96) ::
      attestArrayOffsetWords origin (dst + 256) n

theorem attestArrayTailWords_length (values : Nat → UInt256) (i n : Nat) :
    (attestArrayTailWords values i n).length = 8 * n := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih =>
      simp only [attestArrayTailWords, List.length_append, attestCellWords, List.length_cons,
        List.length_nil, ih]
      omega

theorem attestArrayOffsetWords_length (origin dst n : Nat) :
    (attestArrayOffsetWords origin dst n).length = n := by
  induction n generalizing dst with
  | zero => rfl
  | succ n ih => simp only [attestArrayOffsetWords, List.length_cons, ih]

theorem attestArrayEncodedMemory_preserves {mem : ByteArray}
    {origin table dst i remaining read len : Nat} {values : Nat → UInt256}
    (htable : table + 32 * remaining ≤ dst) (hin : read + len ≤ mem.size)
    (hbelow : read + len ≤ dst)
    (hdis : read + len ≤ table ∨ table + 32 * remaining ≤ read) :
    (attestArrayEncodedMemory mem origin table dst values i remaining).readWithPadding read len =
      mem.readWithPadding read len := by
  induction remaining generalizing mem table dst i with
  | zero => rfl
  | succ remaining ih =>
      rw [attestArrayEncodedMemory, ih (by omega)
        (by rw [attestArrayItemEncodedMemory_size _ _ _ _ _ (by omega)]; omega)
        (by omega) (by omega)]
      exact attestArrayItemEncodedMemory_preserves hin hbelow (by omega)

theorem attestArrayEncodedMemory_read_table (mem : ByteArray)
    (origin table dst i remaining : Nat) (values : Nat → UInt256)
    (htable : table + 32 * remaining ≤ dst) :
    (attestArrayEncodedMemory mem origin table dst values i remaining).readWithPadding table
      (32 * remaining) = wordBytes (attestArrayOffsetWords origin dst remaining) := by
  induction remaining generalizing mem table dst i with
  | zero => simp only [Nat.mul_zero, byteArray_readWithPadding_zero,
      attestArrayOffsetWords, wordBytes]
  | succ remaining ih =>
      have hsz := attestArrayEncodedMemory_size (mem := mem) (origin := origin)
        (i := i) (values := values) htable (by omega)
      have hin : table + 32 + 32 * remaining ≤
          (attestArrayEncodedMemory mem origin table dst values i (remaining + 1)).size := by
        rw [hsz]; omega
      rw [show 32 * (remaining + 1) = 32 + 32 * remaining by omega,
        readWithPadding_split _ _ _ _ hin, attestArrayEncodedMemory]
      rw [attestArrayEncodedMemory_preserves (by omega)
        (by rw [attestArrayItemEncodedMemory_size _ _ _ _ _ (by omega)]; omega)
        (by omega) (.inl (by omega)), attestArrayItemEncodedMemory_read_table (by omega),
        ih _ _ _ _ (by omega)]
      rfl

theorem attestArrayEncodedMemory_read_tail (mem : ByteArray)
    (origin table dst i remaining : Nat) (values : Nat → UInt256)
    (htable : table + 32 * remaining ≤ dst) :
    (attestArrayEncodedMemory mem origin table dst values i remaining).readWithPadding dst
      (256 * remaining) = wordBytes (attestArrayTailWords values i remaining) := by
  induction remaining generalizing mem table dst i with
  | zero => simp only [Nat.mul_zero, byteArray_readWithPadding_zero,
      attestArrayTailWords, wordBytes]
  | succ remaining ih =>
      have hsz := attestArrayEncodedMemory_size (mem := mem) (origin := origin)
        (i := i) (values := values) htable (by omega)
      have hin : dst + 256 + 256 * remaining ≤
          (attestArrayEncodedMemory mem origin table dst values i (remaining + 1)).size := by
        rw [hsz]; omega
      rw [Nat.mul_succ, Nat.add_comm (256 * remaining),
        readWithPadding_split _ _ _ _ hin, attestArrayEncodedMemory]
      rw [attestArrayEncodedMemory_preserves (by omega)
        (by rw [attestArrayItemEncodedMemory_size _ _ _ _ _ (by omega)]; omega)
        (by omega) (.inr (by omega)), attestArrayItemEncodedMemory_read_body,
        ih _ _ _ _ (by omega), attestArrayTailWords, wordBytes_append]

end Benchmarks.EAS.Attester
