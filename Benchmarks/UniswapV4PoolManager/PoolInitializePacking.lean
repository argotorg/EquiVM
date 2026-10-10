import Benchmarks.UniswapV4PoolManager.PoolInitializeSource
import Benchmarks.UniswapV4PoolManager.WordFieldPacking
import Benchmarks.UniswapV4PoolManager.PoolLPFeeTrace

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV4PoolManager
set_option maxRecDepth 5000

theorem slot0SetSqrtZero (price : UInt256) : slot0SetSqrtWord ⟨0⟩ price = price := by
  apply u256_inj
  simp only [slot0SetSqrtWord, u256_lor_toNat_exact, uland_toNat,
    wordShiftLeftNat _ (by decide : 0 < 256)]
  change (0 &&& sqrtPriceClearMask.toNat) ||| ((price.toNat * 2^0) % UInt256.size) = price.toNat
  simp only [Nat.zero_and, Nat.zero_or, pow_zero, Nat.mul_one]
  exact Nat.mod_eq_of_lt price.val.isLt

theorem poolInitializeWord_compiled {price tick fee : UInt256}
    (hp : price.toNat < 2^160) (hf : fee.toNat < 2^24) :
    UInt256.lor (UInt256.lor
      (UInt256.land (UInt256.shiftLeft tick (UInt256.ofNat 160))
        (UInt256.ofNat 24519927192352584402830634230720114221616806299005091840)) price)
      (UInt256.land (UInt256.shiftLeft fee (UInt256.ofNat 208))
        (UInt256.ofNat 6901745935414424457133245323534729813113482726486420146767558386647040)) =
      poolInitializeWord price tick fee := by
  let tickMask : UInt256 := UInt256.ofNat (2^24-1)
  let tickFieldMask : UInt256 := UInt256.ofNat 24519927192352584402830634230720114221616806299005091840
  have hmask : UInt256.shiftLeft tickMask (UInt256.ofNat 160) = tickFieldMask := by decide +kernel
  have hp0 := solcAddrMask_clean hp
  have hpt : UInt256.land price tickClearMask = price :=
    wordMaskPreservesSubmask hp0 (by decide +kernel)
  have hpf : UInt256.land price lpFeeClearMask = price :=
    wordMaskPreservesSubmask hp0 (by decide +kernel)
  have ht : UInt256.land (UInt256.shiftLeft tick (UInt256.ofNat 160)) tickFieldMask =
      UInt256.shiftLeft (UInt256.land tick tickMask) (UInt256.ofNat 160) := by
    simpa only [hmask] using wordShiftAnd tick tickMask (by decide : 160 < 256)
  have htm : UInt256.land (UInt256.land tick tickMask) tickMask = UInt256.land tick tickMask := by
    apply u256_inj
    simp only [uland_toNat, Nat.and_assoc, Nat.and_self]
  have htf : UInt256.land (UInt256.shiftLeft (UInt256.land tick tickMask) (UInt256.ofNat 160))
      lpFeeClearMask = UInt256.shiftLeft (UInt256.land tick tickMask) (UInt256.ofNat 160) := by
    apply wordMaskPreservesSubmask (submask := tickFieldMask) ?_ (by decide +kernel)
    have h := wordShiftAnd (UInt256.land tick tickMask) tickMask (by decide : 160 < 256)
    rw [hmask, htm] at h
    exact h
  dsimp only [tickMask] at htf
  have hfee : UInt256.land (UInt256.shiftLeft fee (UInt256.ofNat 208))
      (UInt256.ofNat 6901745935414424457133245323534729813113482726486420146767558386647040) =
      UInt256.shiftLeft fee (UInt256.ofNat 208) := by
    rw [u256_land_comm]
    exact lpFeeShiftMaskClean fee hf
  rw [hfee, ht]
  simp only [poolInitializeWord, slot0SetSqrtZero, slot0SetTickWord, slot0LPFeeWord,
    hpt, wordLandOr, hpf, htf]
  rw [u256_lor_comm price]
  rfl

end Benchmarks.UniswapV4PoolManager
