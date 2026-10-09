import Benchmarks.EAS.Attester.PairRequestsEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: word-level view of the nested pair-array ABI encoding.
def pairRequestWords (schema : UInt256) (n : Nat) (values : Nat → UInt256 × UInt256) : List UInt256
    :=
  [schema, UInt256.ofNat 64, UInt256.ofNat n] ++ pairSequenceWords values 0 n

theorem pairRequestWords_length (schema : UInt256) (n : Nat) (values : Nat → UInt256 × UInt256) :
    (pairRequestWords schema n values).length = 3 + 2 * n := by
  simp only [pairRequestWords, List.length_append, List.length_cons, List.length_nil,
    pairSequenceWords_length]

theorem pairRequestEncodedMemory_eq (mem : ByteArray) (origin table dst : Nat) (schema : UInt256)
    (n : Nat) (values : Nat → UInt256 × UInt256) :
    pairRequestEncodedMemory mem origin table dst schema n values =
      wordSequenceMemory (writeWord mem table (UInt256.ofNat (dst - origin - 64))) dst
        (pairRequestWords schema n values) := by
  simp only [pairRequestEncodedMemory, pairRequestHeaderMemory, pairRequestWords, writeCascade,
    List.cons_append, List.nil_append, wordSequenceMemory, Nat.add_assoc, Nat.reduceAdd]

theorem pairRequestEncodedMemory_read_body (mem : ByteArray) (origin table dst : Nat)
    (schema : UInt256) (n : Nat) (values : Nat → UInt256 × UInt256) :
    (pairRequestEncodedMemory mem origin table dst schema n values).readWithPadding dst
      (96 + 64 * n) = wordBytes (pairRequestWords schema n values) := by
  rw [pairRequestEncodedMemory_eq]
  have hread := wordSequenceMemory_read
    (writeWord mem table (UInt256.ofNat (dst - origin - 64))) dst (pairRequestWords schema n values)
  rw [pairRequestWords_length, show 32 * (3 + 2 * n) = 96 + 64 * n by omega] at hread
  exact hread

theorem pairRequestEncodedMemory_read_table {mem : ByteArray} {origin table dst n : Nat}
    {schema : UInt256} {values : Nat → UInt256 × UInt256} (ht : table + 32 ≤ dst) :
    (pairRequestEncodedMemory mem origin table dst schema n values).readWithPadding table 32 =
      (UInt256.ofNat (dst - origin - 64)).toByteArray := by
  rw [pairRequestEncodedMemory_eq, wordSequenceMemory_read_below_unbounded _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) ht, writeWord_sparse_read_back]

theorem pairRequestEncodedMemory_preserves {mem : ByteArray} {origin table dst n read len : Nat}
    {schema : UInt256} {values : Nat → UInt256 × UInt256}
    (hin : read + len ≤ mem.size) (hbelow : read + len ≤ dst)
    (hdis : read + len ≤ table ∨ table + 32 ≤ read) :
    (pairRequestEncodedMemory mem origin table dst schema n values).readWithPadding read len =
      mem.readWithPadding read len := by
  rw [pairRequestEncodedMemory_eq, wordSequenceMemory_read_below_unbounded _ _ _ _ _
    (by rw [writeWord_sparse_size]; omega) hbelow]
  exact writeWord_sparse_read_preserved_unbounded _ _ _ _ _ hin hdis

def pairRequestsTailWords (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256 × UInt256) (i : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => pairRequestWords (schemas i) (counts i) (values i) ++
      pairRequestsTailWords schemas counts values (i + 1) n

def pairRequestsOffsetWords (origin dst : Nat) (counts : Nat → Nat) (i : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => UInt256.ofNat (dst - origin - 64) ::
      pairRequestsOffsetWords origin (dst + 96 + 64 * counts i) counts (i + 1) n

theorem pairRequestsOffsetWords_length (origin dst : Nat) (counts : Nat → Nat) (i n : Nat) :
    (pairRequestsOffsetWords origin dst counts i n).length = n := by
  induction n generalizing dst i with
  | zero => rfl
  | succ n ih => simp only [pairRequestsOffsetWords, List.length_cons, ih]

theorem pairRequestsEncodedEnd_eq (dst : Nat) (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256 × UInt256) (i n : Nat) :
    pairRequestsEncodedEnd dst counts i n =
      dst + 32 * (pairRequestsTailWords schemas counts values i n).length := by
  induction n generalizing dst i with
  | zero => rfl
  | succ n ih =>
      rw [pairRequestsEncodedEnd, ih, pairRequestsTailWords, List.length_append,
        pairRequestWords_length]
      omega

theorem pairRequestsEncodedMemory_size {mem : ByteArray} {origin table dst i remaining : Nat}
    {schemas : Nat → UInt256} {counts : Nat → Nat} {values : Nat → Nat → UInt256 × UInt256}
    (htable : table + 32 * remaining ≤ dst) (hz : remaining = 0 → dst ≤ mem.size) :
    (pairRequestsEncodedMemory mem origin table dst schemas counts values i remaining).size =
      max mem.size (pairRequestsEncodedEnd dst counts i remaining) := by
  induction remaining generalizing mem table dst i with
  | zero => simp only [pairRequestsEncodedMemory, pairRequestsEncodedEnd]; omega
  | succ remaining ih =>
      have hsz := pairRequestEncodedMemory_size (mem := mem) (origin := origin)
        (table := table) (dst := dst) (schema := schemas i) (n := counts i) (values := values i)
        (by omega)
      have hend := pairRequestsEncodedEnd_lower (dst + 96 + 64 * counts i) counts (i + 1) remaining
      rw [pairRequestsEncodedMemory, pairRequestsEncodedEnd,
          ih (by omega) (by intro _; rw [hsz]; omega), hsz]
      omega

theorem pairRequestsEncodedMemory_preserves {mem : ByteArray} {origin table dst i remaining read len
    : Nat}
    {schemas : Nat → UInt256} {counts : Nat → Nat} {values : Nat → Nat → UInt256 × UInt256}
    (htable : table + 32 * remaining ≤ dst) (hin : read + len ≤ mem.size)
    (hbelow : read + len ≤ dst)
    (hdis : read + len ≤ table ∨ table + 32 * remaining ≤ read) :
    (pairRequestsEncodedMemory mem origin table dst schemas counts values i
        remaining).readWithPadding
      read len = mem.readWithPadding read len := by
  induction remaining generalizing mem table dst i with
  | zero => rfl
  | succ remaining ih =>
      rw [pairRequestsEncodedMemory, ih (by omega)
        (by rw [pairRequestEncodedMemory_size (by omega)]; omega) (by omega) (by omega)]
      exact pairRequestEncodedMemory_preserves hin hbelow (by omega)

theorem pairRequestsEncodedMemory_read_table (mem : ByteArray) (origin table dst i remaining : Nat)
    (schemas : Nat → UInt256) (counts : Nat → Nat) (values : Nat → Nat → UInt256 × UInt256)
    (htable : table + 32 * remaining ≤ dst) :
    (pairRequestsEncodedMemory mem origin table dst schemas counts values i
        remaining).readWithPadding
      table (32 * remaining) = wordBytes (pairRequestsOffsetWords origin dst counts i remaining) :=
          by
  induction remaining generalizing mem table dst i with
  | zero => simp only [Nat.mul_zero, byteArray_readWithPadding_zero, pairRequestsOffsetWords,
      wordBytes]
  | succ remaining ih =>
      have hsz := pairRequestsEncodedMemory_size (mem := mem) (origin := origin) (i := i)
        (schemas := schemas) (counts := counts) (values := values) htable (by omega)
      have hend := pairRequestsEncodedEnd_lower dst counts i (remaining + 1)
      have hin : table + 32 + 32 * remaining ≤
          (pairRequestsEncodedMemory mem origin table dst schemas counts values i (remaining +
              1)).size := by
        rw [hsz]; omega
      rw [show 32 * (remaining + 1) = 32 + 32 * remaining by omega,
        readWithPadding_split _ _ _ _ hin, pairRequestsEncodedMemory]
      rw [pairRequestsEncodedMemory_preserves (by omega)
        (by rw [pairRequestEncodedMemory_size (by omega)]; omega) (by omega) (.inl (by omega)),
        pairRequestEncodedMemory_read_table (by omega), ih _ _ _ _ (by omega)]
      rfl

theorem pairRequestsEncodedMemory_read_tail (mem : ByteArray) (origin table dst i remaining : Nat)
    (schemas : Nat → UInt256) (counts : Nat → Nat) (values : Nat → Nat → UInt256 × UInt256)
    (htable : table + 32 * remaining ≤ dst) :
    (pairRequestsEncodedMemory mem origin table dst schemas counts values i
        remaining).readWithPadding
      dst (32 * (pairRequestsTailWords schemas counts values i remaining).length) =
        wordBytes (pairRequestsTailWords schemas counts values i remaining) := by
  induction remaining generalizing mem table dst i with
  | zero => simp only [pairRequestsTailWords, List.length_nil, Nat.mul_zero,
      byteArray_readWithPadding_zero, wordBytes]
  | succ remaining ih =>
      have hsz := pairRequestsEncodedMemory_size (mem := mem) (origin := origin) (i := i)
        (schemas := schemas) (counts := counts) (values := values) htable (by omega)
      rw [pairRequestsEncodedEnd_eq _ schemas counts values] at hsz
      have hin : dst + (96 + 64 * counts i) +
          32 * (pairRequestsTailWords schemas counts values (i + 1) remaining).length ≤
          (pairRequestsEncodedMemory mem origin table dst schemas counts values i (remaining +
              1)).size := by
        rw [hsz, pairRequestsTailWords, List.length_append, pairRequestWords_length]; omega
      rw [pairRequestsTailWords, List.length_append, Nat.mul_add, pairRequestWords_length,
        show 32 * (3 + 2 * counts i) = 96 + 64 * counts i by omega,
        readWithPadding_split _ _ _ _ hin, pairRequestsEncodedMemory]
      rw [pairRequestsEncodedMemory_preserves (by omega)
        (by rw [pairRequestEncodedMemory_size (by omega)]; omega) (by omega) (.inr (by omega)),
        pairRequestEncodedMemory_read_body]
      rw [show dst + (96 + 64 * counts i) = dst + 96 + 64 * counts i by omega,
        ih _ _ _ _ (by omega), wordBytes_append]

def pairRequestsABIWords (origin n : Nat) (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256 × UInt256) : List UInt256 :=
  [UInt256.ofNat 32, UInt256.ofNat n] ++
    pairRequestsOffsetWords origin (origin + 64 + 32 * n) counts 0 n ++
    pairRequestsTailWords schemas counts values 0 n

theorem pairRequestsABIHeaderMemory_size (mem : ByteArray) (origin n : Nat) :
    (pairRequestsABIHeaderMemory mem origin n).size = max mem.size (origin + 64) := by
  simp only [pairRequestsABIHeaderMemory, writeCascade, writeWord_sparse_size]
  omega

theorem pairRequestsABIHeaderMemory_read (mem : ByteArray) (origin n : Nat) :
    (pairRequestsABIHeaderMemory mem origin n).readWithPadding origin 64 =
      wordBytes [UInt256.ofNat 32, UInt256.ofNat n] :=
  wordSequenceMemory_read mem origin [UInt256.ofNat 32, UInt256.ofNat n]

theorem pairRequestsABIMemory_size (mem : ByteArray) (origin n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256 × UInt256) :
    (pairRequestsABIMemory mem origin n schemas counts values).size =
      max mem.size (pairRequestsABIEnd origin n counts) := by
  have he := pairRequestsEncodedEnd_lower (origin + 64 + 32 * n) counts 0 n
  rw [pairRequestsABIMemory, pairRequestsEncodedMemory_size (by omega)
    (by intro hn; subst n; rw [pairRequestsABIHeaderMemory_size]; omega),
    pairRequestsABIHeaderMemory_size]
  unfold pairRequestsABIEnd
  omega

theorem pairRequestsABIWords_length (origin n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256 × UInt256) :
    32 * (pairRequestsABIWords origin n schemas counts values).length =
      64 + 32 * n + 32 * (pairRequestsTailWords schemas counts values 0 n).length := by
  simp only [pairRequestsABIWords, List.length_append, List.length_cons, List.length_nil,
    pairRequestsOffsetWords_length]
  omega

theorem pairRequestsABIMemory_read (mem : ByteArray) (origin n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256 × UInt256) :
    (pairRequestsABIMemory mem origin n schemas counts values).readWithPadding origin
      (32 * (pairRequestsABIWords origin n schemas counts values).length) =
        wordBytes (pairRequestsABIWords origin n schemas counts values) := by
  have hsize := pairRequestsABIMemory_size mem origin n schemas counts values
  rw [pairRequestsABIEnd, pairRequestsEncodedEnd_eq _ schemas counts values] at hsize
  have hin : origin + 64 + 32 * n +
      32 * (pairRequestsTailWords schemas counts values 0 n).length ≤
      (pairRequestsABIMemory mem origin n schemas counts values).size := by rw [hsize]; omega
  have hhead : (pairRequestsABIMemory mem origin n schemas counts values).readWithPadding origin 64
      =
      wordBytes [UInt256.ofNat 32, UInt256.ofNat n] := by
    rw [pairRequestsABIMemory, pairRequestsEncodedMemory_preserves (by omega)
      (by rw [pairRequestsABIHeaderMemory_size]; omega) (by omega) (.inl (by omega)),
      pairRequestsABIHeaderMemory_read]
  rw [pairRequestsABIWords_length,
    show 64 + 32 * n + 32 * (pairRequestsTailWords schemas counts values 0 n).length =
      64 + (32 * n + 32 * (pairRequestsTailWords schemas counts values 0 n).length) by omega,
    readWithPadding_split _ _ _ _ (by omega), hhead,
    readWithPadding_split _ _ _ _ hin]
  rw [pairRequestsABIMemory,
    pairRequestsEncodedMemory_read_table (pairRequestsABIHeaderMemory mem origin n)
      origin (origin + 64) (origin + 64 + 32 * n) 0 n schemas counts values (by omega),
    pairRequestsEncodedMemory_read_tail (pairRequestsABIHeaderMemory mem origin n)
      origin (origin + 64) (origin + 64 + 32 * n) 0 n schemas counts values (by omega)]
  simp only [pairRequestsABIWords, wordBytes_append, ByteArray.append_assoc]

theorem pairRequestsABIMemory_read_below {mem : ByteArray} {origin n read len : Nat}
    {schemas : Nat → UInt256} {counts : Nat → Nat}
    {values : Nat → Nat → UInt256 × UInt256}
    (hin : read + len ≤ mem.size) (hbelow : read + len ≤ origin) :
    (pairRequestsABIMemory mem origin n schemas counts values).readWithPadding read len =
      mem.readWithPadding read len := by
  rw [pairRequestsABIMemory, pairRequestsEncodedMemory_preserves (by omega)
    (by rw [pairRequestsABIHeaderMemory_size]; omega) (by omega) (.inl (by omega))]
  apply writeCascade_read_preserved_unbounded _ _ _ _ hin
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> exact .inl (by dsimp; omega)

end Reasoning.Theory
