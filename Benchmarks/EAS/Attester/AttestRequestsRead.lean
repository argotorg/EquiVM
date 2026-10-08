import Benchmarks.EAS.Attester.AttestRequestRead
import Benchmarks.EAS.Attester.PairRequestsRead

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestRequestsTailWords (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) (i : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => attestBatchRowWords (schemas i) (counts i) (values i) ++
      attestRequestsTailWords schemas counts values (i + 1) n

def attestRequestsOffsetWords (origin dst : Nat) (counts : Nat → Nat) (i : Nat) : Nat → List UInt256
  | 0 => []
  | n + 1 => UInt256.ofNat (dst - origin - 64) ::
      attestRequestsOffsetWords origin (dst + 96 + 288 * counts i) counts (i + 1) n

theorem attestRequestsOffsetWords_length (origin dst : Nat) (counts : Nat → Nat) (i n : Nat) :
    (attestRequestsOffsetWords origin dst counts i n).length = n := by
  induction n generalizing dst i with
  | zero => rfl
  | succ n ih => simp only [attestRequestsOffsetWords, List.length_cons, ih]

theorem attestRequestsEncodedEnd_eq (dst : Nat) (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) (i n : Nat) :
    attestRequestsEncodedEnd dst counts i n =
      dst + 32 * (attestRequestsTailWords schemas counts values i n).length := by
  induction n generalizing dst i with
  | zero => rfl
  | succ n ih =>
      rw [attestRequestsEncodedEnd, ih, attestRequestsTailWords, List.length_append,
        attestBatchRowWords_length]
      omega

theorem attestRequestsEncodedMemory_size_lower {mem : ByteArray}
    {origin table dst i remaining : Nat} {schemas : Nat → UInt256} {counts : Nat → Nat}
    {values : Nat → Nat → UInt256} (htable : table + 32 * remaining ≤ dst)
    (hz : remaining = 0 → dst ≤ mem.size) :
    attestRequestsEncodedEnd dst counts i remaining ≤
      (attestRequestsEncodedMemory mem origin table dst schemas counts values i remaining).size :=
          by
  induction remaining generalizing mem table dst i with
  | zero => exact hz rfl
  | succ remaining ih =>
      have hsz := attestRequestEncodedMemory_size_lower (mem := mem) (origin := origin)
        (table := table) (dst := dst) (schema := schemas i) (n := counts i) (values := values i)
        (by omega)
      exact ih (by omega) (by intro _; exact hsz)

theorem attestRequestsEncodedMemory_size {mem : ByteArray}
    {origin table dst i remaining : Nat} {schemas : Nat → UInt256} {counts : Nat → Nat}
    {values : Nat → Nat → UInt256} (htable : table + 32 * remaining ≤ dst)
    (hn : 0 < remaining) (hc : ∀ j, i ≤ j → j < i + remaining → 0 < counts j) :
    (attestRequestsEncodedMemory mem origin table dst schemas counts values i remaining).size =
      max mem.size (attestRequestsEncodedEnd dst counts i remaining + 32) := by
  induction remaining generalizing mem table dst i with
  | zero => omega
  | succ remaining ih =>
      have hi := hc i (by omega) (by omega)
      rw [attestRequestsEncodedMemory, attestRequestsEncodedEnd]
      cases remaining with
      | zero =>
          simp only [attestRequestsEncodedMemory, attestRequestsEncodedEnd]
          exact attestRequestEncodedMemory_size (by omega) hi
      | succ remaining =>
          rw [ih (by omega) (by omega) (by intro j hj hj'; exact hc j (by omega) (by omega)),
            attestRequestEncodedMemory_size (by omega) hi]
          have he := attestRequestsEncodedEnd_lower (dst + 96 + 288 * counts i)
            counts (i + 1) (remaining + 1)
          omega

theorem attestRequestsEncodedMemory_preserves {mem : ByteArray} {origin table dst i remaining read
    len : Nat}
    {schemas : Nat → UInt256} {counts : Nat → Nat} {values : Nat → Nat → UInt256}
    (htable : table + 32 * remaining ≤ dst) (hin : read + len ≤ mem.size)
    (hbelow : read + len ≤ dst)
    (hdis : read + len ≤ table ∨ table + 32 * remaining ≤ read) :
    (attestRequestsEncodedMemory mem origin table dst schemas counts values i
        remaining).readWithPadding
      read len = mem.readWithPadding read len := by
  induction remaining generalizing mem table dst i with
  | zero => rfl
  | succ remaining ih =>
      rw [attestRequestsEncodedMemory, ih (by omega)
        (by
          have hs := attestRequestEncodedMemory_mem_size mem origin table dst
            (counts i) (schemas i) (values i)
          omega) (by omega) (by omega)]
      exact attestRequestEncodedMemory_preserves hin hbelow (by omega)

theorem attestRequestsEncodedMemory_read_table (mem : ByteArray) (origin table dst i remaining :
    Nat)
    (schemas : Nat → UInt256) (counts : Nat → Nat) (values : Nat → Nat → UInt256)
    (htable : table + 32 * remaining ≤ dst) :
    (attestRequestsEncodedMemory mem origin table dst schemas counts values i
        remaining).readWithPadding
      table (32 * remaining) = wordBytes (attestRequestsOffsetWords origin dst counts i remaining)
          := by
  induction remaining generalizing mem table dst i with
  | zero => simp only [Nat.mul_zero, byteArray_readWithPadding_zero, attestRequestsOffsetWords,
      wordBytes]
  | succ remaining ih =>
      have hsz := attestRequestsEncodedMemory_size_lower (mem := mem) (origin := origin) (i := i)
        (schemas := schemas) (counts := counts) (values := values) htable (by omega)
      have hend := attestRequestsEncodedEnd_lower dst counts i (remaining + 1)
      have hin : table + 32 + 32 * remaining ≤
          (attestRequestsEncodedMemory mem origin table dst schemas counts values i (remaining +
              1)).size := by
        omega
      rw [show 32 * (remaining + 1) = 32 + 32 * remaining by omega,
        readWithPadding_split _ _ _ _ hin, attestRequestsEncodedMemory]
      rw [attestRequestsEncodedMemory_preserves (by omega)
        (by
          have hs := attestRequestEncodedMemory_size_lower (mem := mem) (origin := origin)
            (table := table) (dst := dst) (schema := schemas i) (n := counts i)
            (values := values i) (by omega)
          omega) (by omega) (.inl (by omega)),
        attestRequestEncodedMemory_read_table (by omega), ih _ _ _ _ (by omega)]
      rfl

theorem attestRequestsEncodedMemory_read_tail (mem : ByteArray) (origin table dst i remaining : Nat)
    (schemas : Nat → UInt256) (counts : Nat → Nat) (values : Nat → Nat → UInt256)
    (htable : table + 32 * remaining ≤ dst) :
    (attestRequestsEncodedMemory mem origin table dst schemas counts values i
        remaining).readWithPadding
      dst (32 * (attestRequestsTailWords schemas counts values i remaining).length) =
        wordBytes (attestRequestsTailWords schemas counts values i remaining) := by
  induction remaining generalizing mem table dst i with
  | zero => simp only [attestRequestsTailWords, List.length_nil, Nat.mul_zero,
      byteArray_readWithPadding_zero, wordBytes]
  | succ remaining ih =>
      have hsz := attestRequestsEncodedMemory_size_lower (mem := mem) (origin := origin) (i := i)
        (schemas := schemas) (counts := counts) (values := values) htable (by omega)
      rw [attestRequestsEncodedEnd_eq _ schemas counts values] at hsz
      have hin : dst + (96 + 288 * counts i) +
          32 * (attestRequestsTailWords schemas counts values (i + 1) remaining).length ≤
          (attestRequestsEncodedMemory mem origin table dst schemas counts values i (remaining +
              1)).size := by
        rw [attestRequestsTailWords, List.length_append, attestBatchRowWords_length] at hsz; omega
      rw [attestRequestsTailWords, List.length_append, Nat.mul_add, attestBatchRowWords_length,
        show 32 * (3 + 9 * counts i) = 96 + 288 * counts i by omega,
        readWithPadding_split _ _ _ _ hin, attestRequestsEncodedMemory]
      rw [attestRequestsEncodedMemory_preserves (by omega)
        (by
          have hs := attestRequestEncodedMemory_size_lower (mem := mem) (origin := origin)
            (table := table) (dst := dst) (schema := schemas i) (n := counts i)
            (values := values i) (by omega)
          omega) (by omega) (.inr (by omega)),
        attestRequestEncodedMemory_read_body _ _ _ _ _ _ _ (by omega)]
      rw [show dst + (96 + 288 * counts i) = dst + 96 + 288 * counts i by omega,
        ih _ _ _ _ (by omega), wordBytes_append]

def attestRequestsABIWords (origin n : Nat) (schemas : Nat → UInt256) (counts : Nat → Nat)
    (values : Nat → Nat → UInt256) : List UInt256 :=
  [UInt256.ofNat 32, UInt256.ofNat n] ++
    attestRequestsOffsetWords origin (origin + 64 + 32 * n) counts 0 n ++
    attestRequestsTailWords schemas counts values 0 n

theorem attestRequestsABIMemory_size_lower (mem : ByteArray) (origin n : Nat)
    (schemas : Nat → UInt256) (counts : Nat → Nat) (values : Nat → Nat → UInt256) :
    attestRequestsABIEnd origin n counts ≤
      (attestRequestsABIMemory mem origin n schemas counts values).size := by
  apply attestRequestsEncodedMemory_size_lower (by omega)
  intro hn
  subst n
  rw [pairRequestsABIHeaderMemory_size]
  omega

theorem attestRequestsABIMemory_size {mem : ByteArray} {origin n : Nat}
    {schemas : Nat → UInt256} {counts : Nat → Nat} {values : Nat → Nat → UInt256}
    (hn : 0 < n) (hc : ∀ j, j < n → 0 < counts j) :
    (attestRequestsABIMemory mem origin n schemas counts values).size =
      max mem.size (attestRequestsABIEnd origin n counts + 32) := by
  have he := attestRequestsEncodedEnd_lower (origin + 64 + 32 * n) counts 0 n
  rw [attestRequestsABIMemory, attestRequestsEncodedMemory_size (by omega) hn
    (by intro j _ hj; exact hc j (by omega)), pairRequestsABIHeaderMemory_size]
  unfold attestRequestsABIEnd
  omega

theorem attestRequestsABIWords_length (origin n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256) :
    32 * (attestRequestsABIWords origin n schemas counts values).length =
      64 + 32 * n + 32 * (attestRequestsTailWords schemas counts values 0 n).length := by
  simp only [attestRequestsABIWords, List.length_append, List.length_cons, List.length_nil,
    attestRequestsOffsetWords_length]
  omega

theorem attestRequestsABIMemory_read (mem : ByteArray) (origin n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256) :
    (attestRequestsABIMemory mem origin n schemas counts values).readWithPadding origin
      (32 * (attestRequestsABIWords origin n schemas counts values).length) =
        wordBytes (attestRequestsABIWords origin n schemas counts values) := by
  have hsize := attestRequestsABIMemory_size_lower mem origin n schemas counts values
  rw [attestRequestsABIEnd, attestRequestsEncodedEnd_eq _ schemas counts values] at hsize
  have hin : origin + 64 + 32 * n +
      32 * (attestRequestsTailWords schemas counts values 0 n).length ≤
      (attestRequestsABIMemory mem origin n schemas counts values).size := by omega
  have hhead : (attestRequestsABIMemory mem origin n schemas counts values).readWithPadding origin
      64 =
      wordBytes [UInt256.ofNat 32, UInt256.ofNat n] := by
    rw [attestRequestsABIMemory, attestRequestsEncodedMemory_preserves (by omega)
      (by rw [pairRequestsABIHeaderMemory_size]; omega) (by omega) (.inl (by omega)),
      pairRequestsABIHeaderMemory_read]
  rw [attestRequestsABIWords_length,
    show 64 + 32 * n + 32 * (attestRequestsTailWords schemas counts values 0 n).length =
      64 + (32 * n + 32 * (attestRequestsTailWords schemas counts values 0 n).length) by omega,
    readWithPadding_split _ _ _ _ (by omega), hhead,
    readWithPadding_split _ _ _ _ hin]
  rw [attestRequestsABIMemory,
    attestRequestsEncodedMemory_read_table (pairRequestsABIHeaderMemory mem origin n)
      origin (origin + 64) (origin + 64 + 32 * n) 0 n schemas counts values (by omega),
    attestRequestsEncodedMemory_read_tail (pairRequestsABIHeaderMemory mem origin n)
      origin (origin + 64) (origin + 64 + 32 * n) 0 n schemas counts values (by omega)]
  simp only [attestRequestsABIWords, wordBytes_append, ByteArray.append_assoc]

theorem attestRequestsABIMemory_read_below {mem : ByteArray} {origin n read len : Nat}
    {schemas : Nat → UInt256} {counts : Nat → Nat}
    {values : Nat → Nat → UInt256}
    (hin : read + len ≤ mem.size) (hbelow : read + len ≤ origin) :
    (attestRequestsABIMemory mem origin n schemas counts values).readWithPadding read len =
      mem.readWithPadding read len := by
  rw [attestRequestsABIMemory, attestRequestsEncodedMemory_preserves (by omega)
    (by rw [pairRequestsABIHeaderMemory_size]; omega) (by omega) (.inl (by omega))]
  apply writeCascade_read_preserved_unbounded _ _ _ _ hin
  intro w hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> exact .inl (by dsimp; omega)

end Benchmarks.EAS.Attester
