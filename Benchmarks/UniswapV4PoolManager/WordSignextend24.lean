import Benchmarks.UniswapV4PoolManager.WordSignedField

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem wordSignBit24 (w : UInt256) :
    UInt256.land w (UInt256.ofNat (2^23)) ≠ ⟨0⟩ ↔ 2^23 ≤ w.toNat % 2^24 :=
  wordSignBitRange w (by decide)

-- LIBRARY CANDIDATE: int24 normalization and byte-index-two sign extension agree.
theorem normalizeSigned24Word (w : UInt256) :
    normalizeInt (.sint ⟨24, by decide⟩) (EVM.signed w) =
      EVM.signed (UInt256.signextend (UInt256.ofNat 2) w) := by
  exact normalizeSignedFieldWord ⟨24, by decide⟩ w

end Benchmarks.UniswapV4PoolManager
