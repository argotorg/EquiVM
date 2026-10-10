import Benchmarks.UniswapV3.Pool.WordSubMask
import Benchmarks.UniswapV3.Pool.SnapshotArithmetic

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

-- LIBRARY CANDIDATE: a minuend may be narrowed before a wrapping unsigned subtraction.
theorem wordSub_land_left (width : ABI.BitWidth) (a b mask : UInt256)
    (hm : mask.toNat = 2 ^ width.val - 1) :
    UInt256.land (UInt256.sub (UInt256.land a mask) b) mask =
      UInt256.land (UInt256.sub a b) mask := by
  have h := normalizeInt_sub_left (.uint width) (Int.ofNat a.toNat) (Int.ofNat b.toNat)
  rw [normalizeUIntWord_mask width a mask hm] at h
  simp only [normalizeUIntInt_mask width _ mask hm, wordOfInt_sub, wordOfInt_ofNat_toNat] at h
  exact u256_inj (Int.ofNat_inj.mp h)

-- LIBRARY CANDIDATE: narrowing both operands commutes with wrapping unsigned subtraction.
theorem wordSub_land_both (width : ABI.BitWidth) (a b mask : UInt256)
    (hm : mask.toNat = 2 ^ width.val - 1) :
    UInt256.land (UInt256.sub (UInt256.land a mask) (UInt256.land b mask)) mask =
      UInt256.land (UInt256.sub a b) mask := by
  rw [wordSub_land_left width _ _ mask hm, wordSub_land_right width _ _ mask hm]

end Benchmarks.UniswapV3.Pool
