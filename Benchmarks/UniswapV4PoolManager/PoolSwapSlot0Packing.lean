import Benchmarks.UniswapV4PoolManager.PoolSwapFinishStorage
import Benchmarks.UniswapV4PoolManager.WordFieldPacking

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem poolSwapSlot0Word_compiled (packed : UInt256) (r : PoolSwapResultWords)
    (hp : r.price.toNat < 2^160) :
    UInt256.lor (UInt256.lor
      (UInt256.land packed (UInt256.ofNat 115792089237316195423546465080034053631536251113206159092519684181958192005120))
      (UInt256.land (UInt256.ofNat 24519927192352584402830634230720114221616806299005091840)
        (UInt256.shiftLeft r.tick (UInt256.ofNat 160))))
      (UInt256.land r.price (UInt256.ofNat 1461501637330902918203684832716283019655932542975)) =
      poolSwapSlot0Word packed r := by
  let tickMask : UInt256 := UInt256.ofNat (2^24-1)
  let fieldMask : UInt256 := UInt256.ofNat 24519927192352584402830634230720114221616806299005091840
  have hmask : UInt256.shiftLeft tickMask (UInt256.ofNat 160) = fieldMask := by decide +kernel
  have ht : UInt256.land fieldMask (UInt256.shiftLeft r.tick (UInt256.ofNat 160)) =
      UInt256.shiftLeft (UInt256.land r.tick tickMask) (UInt256.ofNat 160) := by
    rw [u256_land_comm]
    simpa only [hmask] using wordShiftAnd r.tick tickMask (by decide : 160 < 256)
  have htm : UInt256.land (UInt256.land r.tick tickMask) tickMask = UInt256.land r.tick tickMask := by
    apply u256_inj
    simp only [uland_toNat, Nat.and_assoc, Nat.and_self]
  have hfield : UInt256.land (UInt256.shiftLeft (UInt256.land r.tick tickMask) (UInt256.ofNat 160))
      sqrtPriceClearMask = UInt256.shiftLeft (UInt256.land r.tick tickMask) (UInt256.ofNat 160) := by
    apply wordMaskPreservesSubmask (submask := fieldMask) ?_ (by decide +kernel)
    simpa only [hmask, htm] using wordShiftAnd (UInt256.land r.tick tickMask) tickMask (by decide : 160 < 256)
  have hclear : UInt256.land (UInt256.land packed tickClearMask) sqrtPriceClearMask =
      UInt256.land packed (UInt256.ofNat 115792089237316195423546465080034053631536251113206159092519684181958192005120) := by
    apply u256_inj
    simp only [uland_toNat, Nat.and_assoc]
    rfl
  have hprice : UInt256.land r.price (UInt256.ofNat 1461501637330902918203684832716283019655932542975) = r.price :=
    solcAddrMask_clean hp
  have hshift : UInt256.shiftLeft r.price (UInt256.ofNat 0) = r.price := by
    apply u256_inj
    rw [wordShiftLeftNat _ (by decide : 0 < 256)]
    simp only [pow_zero, Nat.mul_one]
    exact Nat.mod_eq_of_lt r.price.val.isLt
  rw [hprice, ht]
  dsimp only [tickMask] at hfield
  simp only [poolSwapSlot0Word, slot0SetSqrtWord, slot0SetTickWord, wordLandOr, hclear, hshift]
  rw [hfield]

end Benchmarks.UniswapV4PoolManager
