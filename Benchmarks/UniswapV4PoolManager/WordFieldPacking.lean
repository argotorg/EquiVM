import Benchmarks.UniswapV4PoolManager.Slot0Source

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager

-- LIBRARY CANDIDATE: a mask preserves any word contained in a preserved submask.
theorem wordMaskPreservesSubmask {word submask mask : UInt256}
    (hw : UInt256.land word submask = word)
    (hm : UInt256.land submask mask = submask) : UInt256.land word mask = word := by
  have hw' := congrArg UInt256.toNat hw
  have hm' := congrArg UInt256.toNat hm
  simp only [uland_toNat] at hw' hm'
  apply u256_inj
  rw [uland_toNat]
  calc
    word.toNat &&& mask.toNat = (word.toNat &&& submask.toNat) &&& mask.toNat := by rw [hw']
    _ = word.toNat &&& submask.toNat := by rw [Nat.and_assoc, hm']
    _ = word.toNat := hw'

-- LIBRARY CANDIDATE: distribute a word mask over the union of packed fields.
theorem wordLandOr (a b mask : UInt256) :
    UInt256.land (UInt256.lor a b) mask = UInt256.lor (UInt256.land a mask) (UInt256.land b mask) := by
  apply u256_inj
  simp only [uland_toNat, u256_lor_toNat_exact, Nat.and_or_distrib_right]

-- LIBRARY CANDIDATE: masking commutes with a common EVM left shift, including truncation.
theorem wordShiftAnd (word mask : UInt256) {n : Nat} (hn : n < 256) :
    UInt256.land (UInt256.shiftLeft word (UInt256.ofNat n)) (UInt256.shiftLeft mask (UInt256.ofNat n)) =
      UInt256.shiftLeft (UInt256.land word mask) (UInt256.ofNat n) := by
  apply u256_inj
  simp only [uland_toNat, wordShiftLeftNat _ hn, ← Nat.shiftLeft_eq]
  change ((word.toNat <<< n) % 2^256) &&& ((mask.toNat <<< n) % 2^256) =
    ((word.toNat &&& mask.toNat) <<< n) % 2^256
  rw [← Nat.and_mod_two_pow, Nat.shiftLeft_and_distrib]

-- LIBRARY CANDIDATE: bits discarded by a left shift can be masked beforehand.
theorem wordShiftLowMask (word mask : UInt256) {n : Nat} (hn : n < 256)
    (hm : mask.toNat = 2^(256-n)-1) :
    UInt256.shiftLeft (UInt256.land word mask) (UInt256.ofNat n) =
      UInt256.shiftLeft word (UInt256.ofNat n) := by
  apply u256_inj
  rw [wordShiftLeftNat _ hn, wordShiftLeftNat _ hn, uland_toNat, hm]
  change (Nat.land word.toNat (2^(256-n)-1)*2^n) % UInt256.size = (word.toNat*2^n) % UInt256.size
  rw [nat_land_mask_eq_mod]
  have hp : 2^256 = 2^(256-n)*2^n := by rw [← Nat.pow_add, Nat.sub_add_cancel (by omega)]
  change ((word.toNat % 2^(256-n))*2^n) % 2^256 = (word.toNat*2^n) % 2^256
  rw [hp, Nat.mul_mod_mul_right, Nat.mul_mod_mul_right, Nat.mod_mod]

end Benchmarks.UniswapV4PoolManager
