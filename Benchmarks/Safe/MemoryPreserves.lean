import Benchmarks.Safe.BytesMemoryPreserved

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: memory growth preserving an existing interval of allocated bytes.
structure MemoryPreserves (before after : ByteArray) (lo hi : Nat) : Prop where
  size : before.size ≤ after.size
  read : ∀ off count, lo ≤ off → off + count ≤ hi → off + count ≤ before.size →
    after.readWithPadding off count = before.readWithPadding off count

theorem MemoryPreserves.refl (mem : ByteArray) (lo hi : Nat) :
    MemoryPreserves mem mem lo hi := ⟨Nat.le_refl _, fun _ _ _ _ _ ↦ rfl⟩

theorem MemoryPreserves.load {before after : ByteArray} {lo hi : Nat}
    (h : MemoryPreserves before after lo hi) (off : UInt256)
    (hl : lo ≤ off.toNat) (hh : off.toNat + 32 ≤ hi)
    (hin : off.toNat + 32 ≤ before.size) : memLoad off after = memLoad off before := by
  rw [memLoadReadWord, h.read off.toNat 32 hl hh hin, ← memLoadReadWord]

theorem MemoryPreserves.trans {a b c : ByteArray} {lo hi hi' : Nat}
    (hab : MemoryPreserves a b lo hi) (hbc : MemoryPreserves b c lo hi') (hh : hi ≤ hi') :
    MemoryPreserves a c lo hi := by
  refine ⟨hab.size.trans hbc.size, ?_⟩
  intro off count hl hu hin
  rw [hbc.read off count hl (hu.trans hh) (hin.trans hab.size), hab.read off count hl hu hin]

theorem MemoryPreserves.scratch (mem : ByteArray) (key slot : UInt256) (hi : Nat) :
    MemoryPreserves mem (twoWordHashMem key slot mem) 96 hi := by
  refine ⟨?_, fun off count hl _ hin ↦ twoWordHashRead _ _ _ _ _ hin (by omega)⟩
  change mem.size ≤ (writeWord (writeWord mem 0 key) 32 slot).size
  rw [writeWord_sparse_size, writeWord_sparse_size]
  omega

-- GENERALIZES twoWordHashMem_read32_above64 from byte reads to a word load.
theorem twoWordHashMem_load_preserved {mem : ByteArray} (key slot off : UInt256)
    (hl : 64 ≤ off.toNat) (hin : off.toNat + 32 ≤ mem.size) :
    memLoad off (twoWordHashMem key slot mem) = memLoad off mem := by
  rw [memLoadReadWord, twoWordHashMem_read32_above64 _ _ hl hin, ← memLoadReadWord]

end Benchmarks.Safe
