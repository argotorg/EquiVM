import Benchmarks.EAS.Attester.AttestCellEncodeMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.EAS.Attester

def attestArrayItemEncodedMemory (mem : ByteArray) (origin table dst : Nat)
    (input : UInt256) : ByteArray :=
  attestCellEncodedMemory (writeWord mem table (UInt256.ofNat (dst - origin - 96))) dst input

theorem attestArrayItemEncodedMemory_prefix (mem : ByteArray) (origin table dst limit : Nat)
    (input : UInt256) (ht : limit ≤ table) (hd : limit ≤ dst) :
    MemoryPrefix mem (attestArrayItemEncodedMemory mem origin table dst input) limit :=
  (memoryPrefix_sparse_writeWord _ _ _ _ (.inl ht)).trans
    ((attestCellEncodedMemory_prefix _ dst input).mono hd)

theorem attestArrayItemEncodedMemory_size (mem : ByteArray) (origin table dst : Nat)
    (input : UInt256) (ht : table + 32 ≤ dst) :
    (attestArrayItemEncodedMemory mem origin table dst input).size = max mem.size (dst + 288) := by
  rw [attestArrayItemEncodedMemory, attestCellEncodedMemory_size, writeWord_sparse_size]
  omega

def attestArrayEncodedMemory (mem : ByteArray) (origin table dst : Nat)
    (values : Nat → UInt256) (i : Nat) : Nat → ByteArray
  | 0 => mem
  | n + 1 => attestArrayEncodedMemory
      (attestArrayItemEncodedMemory mem origin table dst (values i)) origin (table + 32)
      (dst + 256) values (i + 1) n

theorem attestArrayEncodedMemory_prefix (mem : ByteArray) (origin table dst limit i n : Nat)
    (values : Nat → UInt256) (ht : limit ≤ table) (hd : limit ≤ dst) :
    MemoryPrefix mem (attestArrayEncodedMemory mem origin table dst values i n) limit := by
  induction n generalizing mem table dst i with
  | zero => exact .refl _ _
  | succ n ih =>
      exact (attestArrayItemEncodedMemory_prefix _ _ _ _ _ _ ht hd).trans
        (ih _ _ _ _ (by omega) (by omega))

theorem attestArrayEncodedMemory_size {mem : ByteArray} {origin table dst i n : Nat}
    {values : Nat → UInt256} (ht : table + 32 * n ≤ dst) (hn : 0 < n) :
    (attestArrayEncodedMemory mem origin table dst values i n).size =
      max mem.size (dst + 256 * n + 32) := by
  induction n generalizing mem table dst i with
  | zero => omega
  | succ n ih =>
      rw [attestArrayEncodedMemory]
      cases n with
      | zero => simpa only [attestArrayEncodedMemory] using
          attestArrayItemEncodedMemory_size mem origin table dst (values i) (by omega)
      | succ n =>
          rw [ih (by omega) (by omega), attestArrayItemEncodedMemory_size _ _ _ _ _ (by omega)]
          omega

end Benchmarks.EAS.Attester
