import Benchmarks.UniswapV3.Pool.OracleTransformMemory

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

theorem oracleDelta_mask_previous (time previous : UInt256) :
    oracleDelta time (UInt256.land previous (UInt256.ofNat (2 ^ 32 - 1))) =
      oracleDelta time previous := by
  apply u256_inj
  apply Int.ofNat_inj.mp
  change Int.ofNat (oracleDelta time (UInt256.land previous (UInt256.ofNat (2 ^ 32 - 1)))).toNat =
    Int.ofNat (oracleDelta time previous).toNat
  rw [← oracleDelta_source, ← oracleDelta_source,
    ← normalizeUIntWord_mask ⟨32, by decide⟩ previous _ (by decide)]
  change (Int.ofNat time.toNat - (Int.ofNat previous.toNat % Int.ofNat (EVM.twoPow 32))) %
    Int.ofNat (EVM.twoPow 32) =
    (Int.ofNat time.toNat - Int.ofNat previous.toNat) % Int.ofNat (EVM.twoPow 32)
  rw [Int.sub_emod, Int.emod_emod, ← Int.sub_emod]

theorem oracleDelta_of_masks {timeRaw previousRaw time previous : UInt256}
    (ht : UInt256.land (UInt256.ofNat 4294967295) timeRaw = time)
    (hp : UInt256.land (UInt256.ofNat 4294967295) previousRaw = previous) :
    UInt256.land (UInt256.ofNat 4294967295) (UInt256.sub timeRaw previousRaw) =
      oracleDelta time previous := by
  have ht' : UInt256.land timeRaw (UInt256.ofNat (2 ^ 32 - 1)) = time := by
    rw [u256_land_comm]; exact ht
  have hp' : UInt256.land previousRaw (UInt256.ofNat (2 ^ 32 - 1)) = previous := by
    rw [u256_land_comm]; exact hp
  rw [u256_land_comm]
  change oracleDelta timeRaw previousRaw = _
  rw [← oracleDelta_mask_time timeRaw previousRaw, ht',
    ← oracleDelta_mask_previous time previousRaw, hp']

end Benchmarks.UniswapV3.Pool
