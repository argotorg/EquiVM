import Benchmarks.CompoundIII.Comet.Common
import Reasoning.HeapMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.CompoundIII.Comet

-- LIBRARY CANDIDATE: transport a complete loaded word across equal read windows.
theorem memLoad_eq_of_read {before after : ByteArray} {ptr : UInt256}
    (hb : ptr.toNat + 32 ≤ before.size) (ha : ptr.toNat + 32 ≤ after.size)
    (hr : after.readWithPadding ptr.toNat 32 = before.readWithPadding ptr.toNat 32) :
    memLoad ptr after = memLoad ptr before := by
  unfold memLoad
  rw [if_neg (by omega), if_neg (by omega), hr]

-- GENERALIZES twoWordHashMem_load_ge to a disjoint write at any offset.
theorem memLoad_writeWord_preserved (mem : ByteArray) (off : Nat) (ptr word : UInt256)
    (hm : ptr.toNat + 32 ≤ mem.size)
    (hd : ptr.toNat + 32 ≤ off ∨ off + 32 ≤ ptr.toNat) :
    memLoad ptr (writeWord mem off word) = memLoad ptr mem := by
  apply memLoad_eq_of_read hm
  · rw [writeWord_sparse_size]; omega
  · apply writeWord_sparse_read_preserved
    exact hd.elim (fun h ↦ Or.inl ⟨h, hm⟩) (fun h ↦ Or.inr ⟨h, hm⟩)

-- GENERALIZES reentrancyMemory_free to a disjoint copy with arbitrary source and destination.
theorem memLoad_copyWindow_preserved (src mem : ByteArray) (srcOff dest len : Nat)
    (ptr : UInt256) (hpos : len ≠ 0) (hsrc : srcOff + len ≤ src.size)
    (hdest : dest ≤ mem.size) (hm : ptr.toNat + 32 ≤ mem.size)
    (hd : ptr.toNat + 32 ≤ dest ∨ dest + len ≤ ptr.toNat) :
    memLoad ptr (src.write srcOff mem dest len) = memLoad ptr mem := by
  apply memLoad_eq_of_read hm
  · rw [copyWindow_size src mem srcOff dest len hpos hsrc hdest]; omega
  · exact copyWindow_read_preserved src mem srcOff dest len ptr.toNat hpos hsrc hdest hm hd

end Benchmarks.CompoundIII.Comet
