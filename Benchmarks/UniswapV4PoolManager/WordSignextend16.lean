import Benchmarks.UniswapV4PoolManager.WordSignedField

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: int16 normalization and byte-index-one sign extension agree.
theorem normalizeSigned16Word (w : UInt256) :
    normalizeInt (.sint ⟨16, by decide⟩) (EVM.signed w) =
      EVM.signed (UInt256.signextend (UInt256.ofNat 1) w) := by
  exact normalizeSignedFieldWord ⟨16, by decide⟩ w

end Benchmarks.UniswapV4PoolManager
