import Benchmarks.EAS.Attester.WordSequenceMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Reasoning.Theory

-- LIBRARY CANDIDATE: ABI encoding of a word and a dynamic array of word pairs.
def pairRequestHeaderMemory (mem : ByteArray) (origin table dst : Nat) (schema : UInt256)
    (n : Nat) : ByteArray :=
  writeCascade mem [(table, UInt256.ofNat (dst - origin - 64)), (dst, schema),
    (dst + 32, UInt256.ofNat 64), (dst + 64, UInt256.ofNat n)]

theorem pairRequestHeaderMemory_prefix (mem : ByteArray) (origin table dst limit n : Nat)
    (schema : UInt256) (ht : limit ≤ table) (hd : limit ≤ dst) :
    MemoryPrefix mem (pairRequestHeaderMemory mem origin table dst schema n) limit := by
  apply memoryPrefix_sparse_cascade
  intro write hw
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> exact .inl (by dsimp; omega)

theorem pairRequestHeaderMemory_size {mem : ByteArray} {origin table dst n : Nat}
    {schema : UInt256} (ht : table + 32 ≤ dst) :
    (pairRequestHeaderMemory mem origin table dst schema n).size = max mem.size (dst + 96) := by
  simp only [pairRequestHeaderMemory, writeCascade, writeWord_sparse_size]
  omega

def pairRequestEncodedMemory (mem : ByteArray) (origin table dst : Nat) (schema : UInt256)
    (n : Nat) (values : Nat → UInt256 × UInt256) : ByteArray :=
  wordSequenceMemory (pairRequestHeaderMemory mem origin table dst schema n) (dst + 96)
    (pairSequenceWords values 0 n)

theorem pairRequestEncodedMemory_prefix (mem : ByteArray) (origin table dst limit n : Nat)
    (schema : UInt256) (values : Nat → UInt256 × UInt256) (ht : limit ≤ table) (hd : limit ≤ dst) :
    MemoryPrefix mem (pairRequestEncodedMemory mem origin table dst schema n values) limit :=
  (pairRequestHeaderMemory_prefix _ _ _ _ _ _ _ ht hd).trans
    ((wordSequenceMemory_prefix _ _ _).mono (by omega))

theorem pairRequestEncodedMemory_size {mem : ByteArray} {origin table dst n : Nat}
    {schema : UInt256} {values : Nat → UInt256 × UInt256} (ht : table + 32 ≤ dst) :
    (pairRequestEncodedMemory mem origin table dst schema n values).size =
      max mem.size (dst + 96 + 64 * n) := by
  rw [pairRequestEncodedMemory, wordSequenceMemory_size _
    (by rw [pairRequestHeaderMemory_size ht]; omega),
    pairRequestHeaderMemory_size ht, pairSequenceWords_length]
  omega

def pairRequestsEncodedMemory (mem : ByteArray) (origin table dst : Nat)
    (schemas : Nat → UInt256) (counts : Nat → Nat) (values : Nat → Nat → UInt256 × UInt256)
    (i : Nat) : Nat → ByteArray
  | 0 => mem
  | remaining + 1 => pairRequestsEncodedMemory
      (pairRequestEncodedMemory mem origin table dst (schemas i) (counts i) (values i))
      origin (table + 32) (dst + 96 + 64 * counts i) schemas counts values (i + 1) remaining

def pairRequestsEncodedEnd (dst : Nat) (counts : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => dst
  | remaining + 1 => pairRequestsEncodedEnd (dst + 96 + 64 * counts i) counts (i + 1) remaining

theorem pairRequestsEncodedEnd_lower (dst : Nat) (counts : Nat → Nat) (i remaining : Nat) :
    dst ≤ pairRequestsEncodedEnd dst counts i remaining := by
  induction remaining generalizing dst i with
  | zero => rfl
  | succ remaining ih =>
      exact le_trans (by omega) (ih _ _)

theorem pairRequestsEncodedEnd_upper {dst i remaining cap : Nat} {counts : Nat → Nat}
    (hc : ∀ j, i ≤ j → j < i + remaining → counts j ≤ cap) :
    pairRequestsEncodedEnd dst counts i remaining ≤ dst + (96 + 64 * cap) * remaining := by
  induction remaining generalizing dst i with
  | zero => simp [pairRequestsEncodedEnd]
  | succ remaining ih =>
      have hh := ih (dst := dst + 96 + 64 * counts i) (i := i + 1)
        (by intro j hj hj'; exact hc j (by omega) (by omega))
      have hi := hc i (by omega) (by omega)
      rw [pairRequestsEncodedEnd, Nat.mul_succ]
      omega

def pairRequestsABIHeaderMemory (mem : ByteArray) (origin n : Nat) : ByteArray :=
  writeCascade mem [(origin, UInt256.ofNat 32), (origin + 32, UInt256.ofNat n)]

def pairRequestsABIMemory (mem : ByteArray) (origin n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256 × UInt256) : ByteArray :=
  pairRequestsEncodedMemory (pairRequestsABIHeaderMemory mem origin n) origin (origin + 64)
    (origin + 64 + 32 * n) schemas counts values 0 n

def pairRequestsABIEnd (origin n : Nat) (counts : Nat → Nat) : Nat :=
  pairRequestsEncodedEnd (origin + 64 + 32 * n) counts 0 n

theorem pairRequestsABIHeaderMemory_prefix (mem : ByteArray) (origin n limit : Nat)
    (hlo : limit ≤ origin) : MemoryPrefix mem (pairRequestsABIHeaderMemory mem origin n) limit := by
  apply memoryPrefix_sparse_cascade
  intro write hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> exact .inl (by dsimp; omega)

end Reasoning.Theory
