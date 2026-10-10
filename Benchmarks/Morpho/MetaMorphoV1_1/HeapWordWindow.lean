import Benchmarks.Morpho.MetaMorphoV1_1.SupplySharesMemoryPrefix

/-! Extend word-wise heap preservation to a whole aligned window. -/

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory

set_option autoImplicit false

theorem memoryPrefix_read_words {before after : ByteArray} {limit : Nat}
    (hp : MemoryPrefix before after limit) (count off : Nat) (hlo : 96 ≤ off)
    (hlimit : off + 32 * count ≤ limit) (hmem : off + 32 * count ≤ before.size) :
    after.readWithPadding off (32 * count) = before.readWithPadding off (32 * count) := by
  induction count generalizing off with
  | zero => simp only [Nat.mul_zero, byteArray_readWithPadding_zero]
  | succ n ih =>
    cases n with
    | zero => exact hp.read off hlo hlimit hmem
    | succ n =>
      rw [show 32 * (n + 1 + 1) = 32 + 32 * (n + 1) by omega,
        byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega)
          (by have := hp.size; omega),
        byteArray_readWithPadding_split_unbounded _ _ _ _ (by decide) (by omega) (by omega),
        hp.read off hlo (by omega) (by omega), ih (off + 32) (by omega) (by omega) (by omega)]

end Benchmarks.Morpho.MetaMorphoV1_1.SourceMemory
