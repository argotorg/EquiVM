import Benchmarks.UniswapV3.Pool.LiquidityDeltaModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a subtrahend may be narrowed before a wrapping unsigned subtraction.
theorem wordSub_land_right (width : ABI.BitWidth) (a b mask : UInt256)
    (hm : mask.toNat = 2 ^ width.val - 1) :
    UInt256.land (UInt256.sub a (UInt256.land b mask)) mask =
      UInt256.land (UInt256.sub a b) mask := by
  have h := normalizeInt_sub_right (.uint width) (Int.ofNat a.toNat) (Int.ofNat b.toNat)
  rw [normalizeUIntWord_mask width b mask hm] at h
  simp only [normalizeUIntInt_mask width _ mask hm, wordOfInt_sub, wordOfInt_ofNat_toNat] at h
  exact u256_inj (Int.ofNat_inj.mp h)

end Benchmarks.UniswapV3.Pool
