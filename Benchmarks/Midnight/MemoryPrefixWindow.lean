import Benchmarks.Midnight.MemoryPrefix

/-! Short byte windows preserved by the word-wise heap relation. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

theorem MemoryPrefix.read_window {before after : ByteArray} {limit off len : Nat}
    (h : MemoryPrefix before after limit) (hlo : 96 ≤ off) (hlim : off + 32 ≤ limit)
    (hin : off + 32 ≤ before.size) (hpos : 0 < len) (hlen : len ≤ 32) :
    after.readWithPadding off len = before.readWithPadding off len := by
  have he := congrArg (fun bytes : ByteArray ↦ bytes.extract 0 len) (h.read off hlo hlim hin)
  dsimp only at he
  rw [readWithPadding_eq_extract _ _ (hin.trans h.size), readWithPadding_eq_extract _ _ hin,
    extract_extract_BA, extract_extract_BA] at he
  rw [readWithPadding_eq_extract_unbounded _ _ _ hpos (by have := h.size; omega),
    readWithPadding_eq_extract_unbounded _ _ _ hpos (by omega)]
  simpa only [Nat.add_zero, Nat.min_eq_left (by omega : off + len ≤ off + 32)] using he

end Benchmarks.Midnight
