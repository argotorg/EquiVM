import Benchmarks.UniswapV4PoolManager.WordSignextend24

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem wordSignBit128 (w : UInt256) :
    UInt256.land w (UInt256.ofNat (2^127)) ≠ ⟨0⟩ ↔ 2^127 ≤ w.toNat % 2^128 :=
  wordSignBitRange w (by decide)

-- LIBRARY CANDIDATE: int128 normalization and byte-index-fifteen sign extension agree.
theorem normalizeSigned128Word (w : UInt256) :
    normalizeInt (.sint ⟨128, by decide⟩) (EVM.signed w) =
      EVM.signed (UInt256.signextend (UInt256.ofNat 15) w) := by
  exact normalizeSignedFieldWord ⟨128, by decide⟩ w

end Benchmarks.UniswapV4PoolManager
