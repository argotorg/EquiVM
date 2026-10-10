import Benchmarks.UniswapV4PoolManager.TickPriceWords

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

def tickPriceGuardWord (sqrtPrice : UInt256) : UInt256 :=
  UInt256.land
    (sqrtPrice + UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007908834511197)
    (UInt256.ofNat 1461501637330902918203684832716283019655932542975)

theorem tickPriceGuardWord_nat (sqrtPrice : UInt256) :
    Int.ofNat (tickPriceGuardWord sqrtPrice).toNat = (Int.ofNat sqrtPrice.toNat-4295128739) % (2^160 : Int) := by
  have hw : sqrtPrice.toNat < 2^256 := sqrtPrice.val.isLt
  have he : Int.ofNat (sqrtPrice + UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007908834511197).toNat %
      (2^160 : Int) = Int.ofNat (tickPriceGuardWord sqrtPrice).toNat :=
    normalizeUintWord ⟨160, by decide⟩ _ _ rfl
  have hn : (UInt256.ofNat 115792089237316195423570985008687907853269984665640564039457584007908834511197).toNat =
      2^256-4295128739 := by decide +kernel
  rw [← he, uadd_toNat, hn]
  simp only [UInt256.size, Int.ofNat_eq_natCast]
  omega

theorem tickPriceGuardWord_le (sqrtPrice : UInt256) (h : ¬tickPriceOutside sqrtPrice) :
    (tickPriceGuardWord sqrtPrice).toNat ≤ 1461446703485210103287273052203988822374428841602 := by
  have he := tickPriceGuardWord_nat sqrtPrice
  unfold tickPriceOutside at h
  simp only [Int.ofNat_eq_natCast] at he h
  omega

theorem tickPriceGuardWord_gt (sqrtPrice : UInt256) (h : tickPriceOutside sqrtPrice) :
    1461446703485210103287273052203988822374428841602 < (tickPriceGuardWord sqrtPrice).toNat := by
  have he := tickPriceGuardWord_nat sqrtPrice
  unfold tickPriceOutside at h
  simp only [Int.ofNat_eq_natCast] at he h
  omega

theorem tickPriceShiftMask (sqrtPrice : UInt256) (hs : sqrtPrice.toNat < 2^160) :
    UInt256.land (UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32))
      (UInt256.ofNat 6277101735386680763835789423207666416102355444459739545600) =
      UInt256.shiftLeft sqrtPrice (UInt256.ofNat 32) := by
  rw [u256_land_comm]
  exact shiftedMaskClean _ _ (bits := 160) (n := 32) (by decide) hs
    (by change sqrtPrice.toNat*2^32 < 2^256; omega) rfl

end Benchmarks.UniswapV4PoolManager
