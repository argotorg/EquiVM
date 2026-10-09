import Benchmarks.EAS.Attester.AttestArrayEncodeMemory
import Benchmarks.EAS.Attester.PairRequestsEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestRequestEncodedMemory (mem : ByteArray) (origin table dst : Nat) (schema : UInt256)
    (n : Nat) (values : Nat → UInt256) : ByteArray :=
  attestArrayEncodedMemory (pairRequestHeaderMemory mem origin table dst schema n)
    dst (dst + 96) (dst + 96 + 32 * n) values 0 n

theorem attestRequestEncodedMemory_prefix (mem : ByteArray) (origin table dst limit n : Nat)
    (schema : UInt256) (values : Nat → UInt256) (ht : limit ≤ table) (hd : limit ≤ dst) :
    MemoryPrefix mem (attestRequestEncodedMemory mem origin table dst schema n values) limit :=
  (pairRequestHeaderMemory_prefix _ _ _ _ _ _ _ ht hd).trans
    (attestArrayEncodedMemory_prefix _ _ _ _ _ _ _ _ (by omega) (by omega))

theorem attestRequestEncodedMemory_size {mem : ByteArray} {origin table dst n : Nat}
    {schema : UInt256} {values : Nat → UInt256} (ht : table + 32 ≤ dst) (hn : 0 < n) :
    (attestRequestEncodedMemory mem origin table dst schema n values).size =
      max mem.size (dst + 96 + 288 * n + 32) := by
  rw [attestRequestEncodedMemory, attestArrayEncodedMemory_size (by omega) hn,
    pairRequestHeaderMemory_size ht]
  omega

def attestRequestsEncodedMemory (mem : ByteArray) (origin table dst : Nat)
    (schemas : Nat → UInt256) (counts : Nat → Nat) (values : Nat → Nat → UInt256)
    (i : Nat) : Nat → ByteArray
  | 0 => mem
  | remaining + 1 => attestRequestsEncodedMemory
      (attestRequestEncodedMemory mem origin table dst (schemas i) (counts i) (values i))
      origin (table + 32) (dst + 96 + 288 * counts i) schemas counts values (i + 1) remaining

def attestRequestsEncodedEnd (dst : Nat) (counts : Nat → Nat) (i : Nat) : Nat → Nat
  | 0 => dst
  | remaining + 1 => attestRequestsEncodedEnd (dst + 96 + 288 * counts i) counts (i + 1) remaining

theorem attestRequestsEncodedEnd_lower (dst : Nat) (counts : Nat → Nat) (i remaining : Nat) :
    dst ≤ attestRequestsEncodedEnd dst counts i remaining := by
  induction remaining generalizing dst i with
  | zero => rfl
  | succ remaining ih =>
      exact le_trans (by omega) (ih _ _)

theorem attestRequestsEncodedEnd_upper {dst i remaining cap : Nat} {counts : Nat → Nat}
    (hc : ∀ j, i ≤ j → j < i + remaining → counts j ≤ cap) :
    attestRequestsEncodedEnd dst counts i remaining ≤ dst + (96 + 288 * cap) * remaining := by
  induction remaining generalizing dst i with
  | zero => simp [attestRequestsEncodedEnd]
  | succ remaining ih =>
      have hh := ih (dst := dst + 96 + 288 * counts i) (i := i + 1)
        (by intro j hj hj'; exact hc j (by omega) (by omega))
      have hi := hc i (by omega) (by omega)
      rw [attestRequestsEncodedEnd, Nat.mul_succ]
      omega

def attestRequestsABIMemory (mem : ByteArray) (origin n : Nat) (schemas : Nat → UInt256)
    (counts : Nat → Nat) (values : Nat → Nat → UInt256) : ByteArray :=
  attestRequestsEncodedMemory (pairRequestsABIHeaderMemory mem origin n) origin (origin + 64)
    (origin + 64 + 32 * n) schemas counts values 0 n

def attestRequestsABIEnd (origin n : Nat) (counts : Nat → Nat) : Nat :=
  attestRequestsEncodedEnd (origin + 64 + 32 * n) counts 0 n

end Benchmarks.EAS.Attester
