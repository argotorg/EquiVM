import Benchmarks.UniswapV4PoolManager.TickPriceWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

theorem tickPriceChoose_canonical {sqrtPrice low high tick : UInt256}
    (hl : int24Canonical low) (hh : int24Canonical high)
    (h : tickPriceChoose sqrtPrice low high = some tick) : int24Canonical tick := by
  unfold tickPriceChoose at h
  split at h
  · cases Option.some.inj h
    exact hl
  · split at h
    · split at h
      · cases Option.some.inj h
        exact hh
      · cases Option.some.inj h
        exact hl
    · contradiction

theorem tickPriceResult_canonical {sqrtPrice tick : UInt256}
    (h : tickPriceResult sqrtPrice = some tick) : int24Canonical tick := by
  unfold tickPriceResult at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · exact tickPriceChoose_canonical (signextend24_canonical _) (signextend24_canonical _) h

-- LIBRARY CANDIDATE: a canonical int24 word has the signed ABI bounds.
theorem int24Canonical_signed_bounds {w : UInt256} (h : int24Canonical w) :
    -(2^23 : Int) ≤ EVM.signed w ∧ EVM.signed w < (2^23 : Int) := by
  have hw : w.toNat < 2^256 := w.val.isLt
  change -(2^23 : Int) ≤ (if w.toNat < 2^255 then (w.toNat : Int) else (w.toNat : Int)-2^256) ∧
    (if w.toNat < 2^255 then (w.toNat : Int) else (w.toNat : Int)-2^256) < (2^23 : Int)
  rcases h with hl | hh
  · rw [if_pos (by omega)]
    omega
  · rw [if_neg (by omega)]
    omega

end Benchmarks.UniswapV4PoolManager
