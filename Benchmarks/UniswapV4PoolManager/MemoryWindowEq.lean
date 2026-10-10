import Benchmarks.UniswapV4PoolManager.WordStoreMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: preserve an allocated memory window and total memory size.
structure MemoryWindowEq (before after : ByteArray) (low high : Nat) : Prop where
  inBounds : high ≤ before.size
  size : after.size = before.size
  read : ∀ off len, low ≤ off → off+len ≤ high →
    after.readWithPadding off len = before.readWithPadding off len

theorem MemoryWindowEq.refl (mem : ByteArray) (low high : Nat) (hi : high ≤ mem.size) :
    MemoryWindowEq mem mem low high := ⟨hi, rfl, fun _ _ _ _ => rfl⟩

theorem MemoryWindowEq.trans {a b c : ByteArray} {low high : Nat}
    (h1 : MemoryWindowEq a b low high) (h2 : MemoryWindowEq b c low high) :
    MemoryWindowEq a c low high :=
  ⟨h1.inBounds, h2.size.trans h1.size, fun off len hlo hhi => (h2.read off len hlo hhi).trans (h1.read off len hlo hhi)⟩

theorem MemoryWindowEq.write (mem : ByteArray) (off : Nat) (word : UInt256) (low high : Nat)
    (hi : high ≤ mem.size) (hw : off+32 ≤ mem.size) (hd : high ≤ off ∨ off+32 ≤ low) :
    MemoryWindowEq mem (writeWord mem off word) low high := by
  refine ⟨hi, ?_, ?_⟩
  · rw [writeWord_sparse_size, Nat.max_eq_left hw]
  · intro read len hlo hhi
    exact writeWord_sparse_read_preserved_unbounded _ _ _ _ _ (by omega) (by omega)

theorem MemoryWindowEq.load {before after : ByteArray} {low high : Nat}
    (h : MemoryWindowEq before after low high) (ptr : UInt256)
    (hlo : low ≤ ptr.toNat) (hhi : ptr.toNat+32 ≤ high) : memLoad ptr after = memLoad ptr before := by
  have hin := h.inBounds
  rw [memLoad, memLoad, if_neg (by rw [h.size]; omega), if_neg (by omega), h.read _ _ hlo hhi]

end Benchmarks.UniswapV4PoolManager
