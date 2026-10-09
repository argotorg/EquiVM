import Benchmarks.Safe.BytesMemory
import Benchmarks.Safe.ModuleMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: transport a length-prefixed byte buffer through preserved reads.
theorem BytesMemory.preserved {mem mem' bytes : ByteArray} {src : Nat}
    (h : BytesMemory mem src bytes) (hb : src < UInt256.size) (hm : mem.size ≤ mem'.size)
    (hr : ∀ off count, src ≤ off → off + count ≤ src + 32 + bytes.size →
      mem'.readWithPadding off count = mem.readWithPadding off count) :
    BytesMemory mem' src bytes := by
  refine ⟨?_, ?_, le_trans h.available hm⟩
  · rw [memLoadReadWord, ulit_toNat' src hb, hr src 32 (by omega) (by omega),
      ← ulit_toNat' src hb, ← memLoadReadWord, h.length]
  · rw [hr (src + 32) bytes.size (by omega) (by omega), h.payload]

theorem BytesMemory.scratch {mem bytes : ByteArray} {src : Nat}
    (h : BytesMemory mem src bytes) (hb : src < UInt256.size) (hs : 64 ≤ src)
    (key slot : UInt256) : BytesMemory (twoWordHashMem key slot mem) src bytes := by
  have hm : 64 ≤ mem.size := by have := h.available; omega
  apply h.preserved hb (by rw [twoWordHashMem_size_of_ge64 _ _ hm])
  intro off count hlo hin
  exact twoWordHashRead _ _ _ _ _ (by have := h.available; omega) (by omega)

end Benchmarks.Safe
