import Benchmarks.Safe.WordArrayMemory
import Benchmarks.Safe.MemoryPreserves

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Safe

-- LIBRARY CANDIDATE: a fully allocated, length-prefixed array of EVM words.
structure WordArrayBuffer (mem : ByteArray) (ptr : Nat) (words : List UInt256) : Prop where
  size : ptr + 32 + 32 * words.length ≤ mem.size
  length : mem.readWithPadding ptr 32 = (UInt256.ofNat words.length).toByteArray
  words : WordArrayMemory mem (ptr + 32) words

theorem WordArrayBuffer.lengthWord {mem ptr words} (h : WordArrayBuffer mem ptr words)
    (hp : ptr < UInt256.size) :
    memLoad (UInt256.ofNat ptr) mem = UInt256.ofNat words.length := by
  rw [memLoadReadWord, ulit_toNat' ptr hp, h.length, uInt256OfByteArray_toByteArray]

theorem WordArrayBuffer.preserved {mem mem' ptr words}
    (h : WordArrayBuffer mem ptr words) (hm : mem.size ≤ mem'.size)
    (hr : ∀ off count, ptr ≤ off → off + count ≤ ptr + 32 + 32 * words.length →
      mem'.readWithPadding off count = mem.readWithPadding off count) :
    WordArrayBuffer mem' ptr words := by
  refine ⟨h.size.trans hm, ?_, ?_⟩
  · rw [hr ptr 32 (by omega) (by omega), h.length]
  · intro i hi
    rw [hr (ptr + 32 + 32 * i) 32 (by omega) (by omega)]
    exact h.words i hi

-- LIBRARY CANDIDATE: the compiler's word-array index arithmetic does not wrap in bounds.
theorem wordArrayIndexAddress (ptr i : Nat) (hb : ptr + 32 + 32 * i < UInt256.size) :
    ((UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i)) +
      UInt256.ofNat ptr).toNat = ptr + 32 + 32 * i := by
  rw [uadd_toNat, uadd_toNat, u256_mul_toNat, ulit_toNat' i (by omega),
    ulit_toNat' ptr (by omega)]
  change ((32 + 32 * i % UInt256.size) % UInt256.size + ptr) % UInt256.size = _
  rw [Nat.mod_eq_of_lt (show 32 * i < UInt256.size by omega),
    Nat.mod_eq_of_lt (show 32 + 32 * i < UInt256.size by omega),
    Nat.mod_eq_of_lt (show 32 + 32 * i + ptr < UInt256.size by omega)]
  omega

theorem WordArrayBuffer.indexWord {mem ptr words} (h : WordArrayBuffer mem ptr words)
    (i : Nat) (hi : i < words.length) (hb : ptr + 32 + 32 * words.length < UInt256.size) :
    memLoad ((UInt256.ofNat 32 + UInt256.mul (UInt256.ofNat 32) (UInt256.ofNat i)) +
      UInt256.ofNat ptr) mem = words[i] := by
  rw [memLoadReadWord, wordArrayIndexAddress ptr i (by omega), h.words i hi,
    uInt256OfByteArray_toByteArray]

end Benchmarks.Safe
