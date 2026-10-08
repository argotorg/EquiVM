import Benchmarks.EAS.Attester.AttestArrayRead
import Benchmarks.EAS.Attester.AttestRequestsEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

theorem attestRequestHeader_eq (mem : ByteArray) (origin table dst : Nat)
    (schema : UInt256) (n : Nat) :
    pairRequestHeaderMemory mem origin table dst schema n =
      wordSequenceMemory (writeWord mem table (UInt256.ofNat (dst - origin - 64))) dst
        [schema, UInt256.ofNat 64, UInt256.ofNat n] := by
  simp only [pairRequestHeaderMemory, writeCascade, wordSequenceMemory,
    Nat.add_assoc, Nat.reduceAdd]

theorem attestRequestEncodedMemory_size_lower {mem : ByteArray} {origin table dst n : Nat}
    {schema : UInt256} {values : Nat → UInt256} (ht : table + 32 ≤ dst) :
    dst + 96 + 288 * n ≤ (attestRequestEncodedMemory mem origin table dst schema n values).size :=
        by
  cases n with
  | zero =>
      simp only [attestRequestEncodedMemory, attestArrayEncodedMemory,
        pairRequestHeaderMemory_size ht, Nat.mul_zero, Nat.add_zero]
      omega
  | succ n => rw [attestRequestEncodedMemory_size ht (by omega)]; omega

theorem attestRequestEncodedMemory_mem_size (mem : ByteArray) (origin table dst n : Nat)
    (schema : UInt256) (values : Nat → UInt256) :
    mem.size ≤ (attestRequestEncodedMemory mem origin table dst schema n values).size :=
  (attestRequestEncodedMemory_prefix mem origin table dst 0 n schema values
    (by omega) (by omega)).size

theorem attestRequestEncodedMemory_preserves {mem : ByteArray}
    {origin table dst n read len : Nat} {schema : UInt256} {values : Nat → UInt256}
    (hin : read + len ≤ mem.size) (hbelow : read + len ≤ dst)
    (hdis : read + len ≤ table ∨ table + 32 ≤ read) :
    (attestRequestEncodedMemory mem origin table dst schema n values).readWithPadding read len =
      mem.readWithPadding read len := by
  rw [attestRequestEncodedMemory, attestArrayEncodedMemory_preserves (by omega)
    (by simp only [pairRequestHeaderMemory, writeCascade, writeWord_sparse_size]; omega)
    (by omega) (.inl (by omega)), attestRequestHeader_eq,
    wordSequenceMemory_read_below_unbounded _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) hbelow]
  exact writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin hdis

theorem attestRequestEncodedMemory_read_table {mem : ByteArray} {origin table dst n : Nat}
    {schema : UInt256} {values : Nat → UInt256} (ht : table + 32 ≤ dst) :
    (attestRequestEncodedMemory mem origin table dst schema n values).readWithPadding table 32 =
      (UInt256.ofNat (dst - origin - 64)).toByteArray := by
  rw [attestRequestEncodedMemory, attestArrayEncodedMemory_preserves (by omega)
    (by rw [pairRequestHeaderMemory_size ht]; omega) (by omega) (.inl (by omega)),
    attestRequestHeader_eq, wordSequenceMemory_read_below_unbounded _ _ _ _ _
      (by rw [writeWord_sparse_size]; omega) ht, writeWord_sparse_read_back]

def attestBatchRowWords (schema : UInt256) (n : Nat) (values : Nat → UInt256) : List UInt256 :=
  [schema, UInt256.ofNat 64, UInt256.ofNat n] ++
    attestArrayOffsetWords 0 (96 + 32 * n) n ++ attestArrayTailWords values 0 n

theorem attestBatchRowWords_length (schema : UInt256) (n : Nat) (values : Nat → UInt256) :
    (attestBatchRowWords schema n values).length = 3 + 9 * n := by
  simp only [attestBatchRowWords, List.length_append, List.length_cons, List.length_nil,
    attestArrayOffsetWords_length, attestArrayTailWords_length]
  omega

theorem attestArrayOffsetWords_translate (origin dst shift n : Nat) :
    attestArrayOffsetWords (origin + shift) (dst + shift) n =
      attestArrayOffsetWords origin dst n := by
  induction n generalizing dst with
  | zero => rfl
  | succ n ih =>
      simp only [attestArrayOffsetWords, Nat.add_sub_add_right]
      rw [show dst + shift + 256 = dst + 256 + shift by omega, ih]

theorem attestRequestEncodedMemory_read_body (mem : ByteArray) (origin table dst : Nat)
    (schema : UInt256) (n : Nat) (values : Nat → UInt256) (ht : table + 32 ≤ dst) :
    (attestRequestEncodedMemory mem origin table dst schema n values).readWithPadding dst
      (96 + 288 * n) = wordBytes (attestBatchRowWords schema n values) := by
  have hsz := attestRequestEncodedMemory_size_lower (mem := mem) (origin := origin)
    (n := n) (schema := schema) (values := values) ht
  have hhead : (attestRequestEncodedMemory mem origin table dst schema n values).readWithPadding
      dst 96 = wordBytes [schema, UInt256.ofNat 64, UInt256.ofNat n] := by
    rw [attestRequestEncodedMemory, attestArrayEncodedMemory_preserves (by omega)
      (by rw [pairRequestHeaderMemory_size ht]; omega) (by omega) (.inl (by omega)),
      attestRequestHeader_eq]
    exact wordSequenceMemory_read _ dst [schema, UInt256.ofNat 64, UInt256.ofNat n]
  rw [show 96 + 288 * n = 96 + (32 * n + 256 * n) by omega,
    readWithPadding_split _ _ _ _ (by omega), hhead,
    readWithPadding_split _ _ _ _ (by omega)]
  rw [attestRequestEncodedMemory, attestArrayEncodedMemory_read_table _ _ _ _ _ _ _ (by omega),
    attestArrayEncodedMemory_read_tail _ _ _ _ _ _ _ (by omega)]
  have hoff : attestArrayOffsetWords dst (dst + 96 + 32 * n) n =
      attestArrayOffsetWords 0 (96 + 32 * n) n := by
    simpa only [Nat.zero_add, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
      attestArrayOffsetWords_translate 0 (96 + 32 * n) dst n
  rw [hoff]
  simp only [attestBatchRowWords, wordBytes_append, ByteArray.append_assoc]

end Benchmarks.EAS.Attester
