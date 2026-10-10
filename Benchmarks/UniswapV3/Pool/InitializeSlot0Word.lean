import Benchmarks.UniswapV3.Pool.InitializeSlot0Model
import Benchmarks.UniswapV3.Pool.PackedPrefixMask
import Benchmarks.UniswapV3.Pool.TickLogBoundsModel

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool

def initializeCompiledPrice (old price : UInt256) : UInt256 :=
  UInt256.lor price (UInt256.land old
    (UInt256.lnot (UInt256.ofNat 1461501637330902918203684832716283019655932542975)))

def initializeCompiledTick (old price tick : UInt256) : UInt256 :=
  UInt256.lor
    (UInt256.mul (UInt256.land (UInt256.signextend (UInt256.ofNat 2) tick)
      (UInt256.ofNat 16777215)) (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))
    (UInt256.land (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 16777215) (UInt256.ofNat 160)))
      (initializeCompiledPrice old price))

def initializeCompiledCardinality (old price tick : UInt256) : UInt256 :=
  UInt256.lor (UInt256.mul (UInt256.ofNat 1)
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 200)))
    (UInt256.land
      (UInt256.ofNat 115792089237210883131926947750643844047320047785756073890994934722613756297215)
      (initializeCompiledTick old price tick))

def initializeCompiledNext (old price tick : UInt256) : UInt256 :=
  UInt256.lor (UInt256.mul (UInt256.ofNat 1)
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 216)))
    (UInt256.land
      (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 65535) (UInt256.ofNat 216)))
      (initializeCompiledCardinality old price tick))

def initializeCompiledWord (old price tick : UInt256) : UInt256 :=
  UInt256.lor (UInt256.land
    (UInt256.ofNat 115339783290479275825761448283253582990243601239149377756565007982906442776575)
    (initializeCompiledNext old price tick))
    (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 240))

theorem initializeCompiledPrice_eq (old price : UInt256) (hp : price.toNat < 2 ^ 160) :
    initializeCompiledPrice old price = packedPrefixWord old price 160 := by
  unfold initializeCompiledPrice
  rw [u256_lor_comm]
  apply u256_inj
  rw [packedMaskedWord_toNat old _ price 0 160 price.toNat (by decide) (by native_decide)
    (by simp only [pow_zero, Nat.mul_one]) hp,
    packedPrefixWord_toNat old price 160 (by decide) hp]
  simp only [pow_zero, Nat.mod_one, Nat.mul_one, Nat.one_mul, Nat.zero_add, Nat.mul_comm]

theorem initializeCompiledTick_eq (old price tick : UInt256) (hp : price.toNat < 2 ^ 160) :
    initializeCompiledTick old price tick =
      packedPrefixWord old (initializeTickLow price (tickLogTick tick)) 184 := by
  have hclean : (UInt256.land (UInt256.signextend (UInt256.ofNat 2) tick)
      (UInt256.ofNat 16777215)).toNat = (EVM.wordOfInt (tickLogTick tick)).toNat % 2 ^ 24 := by
    rw [tickLogSignextend, uland_toNat]
    exact nat_land_mask_eq_mod _ 24
  have hfit : (EVM.wordOfInt (tickLogTick tick)).toNat % 2 ^ 24 < 2 ^ 24 :=
    Nat.mod_lt _ (by positivity)
  unfold initializeCompiledTick
  rw [initializeCompiledPrice_eq old price hp, u256_lor_comm, u256_land_comm]
  apply packedPrefixWord_masked old price _ _ _ 160 24
    ((EVM.wordOfInt (tickLogTick tick)).toNat % 2 ^ 24) (by decide) hp (by native_decide)
  · have hshift : (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)).toNat = 2 ^ 160 :=
      by decide
    change UInt256.toNat ((_ : UInt256) * _) = _
    rw [umul_toNat _ _ (by rw [hclean, hshift]; change _ < 2 ^ 256; omega), hclean, hshift]
  · exact hfit
  · exact packedAppend_toNat price _ 160 24 (by decide) hp

theorem initializeCompiledCardinality_eq (old price tick : UInt256) (hp : price.toNat < 2 ^ 160) :
    initializeCompiledCardinality old price tick =
      packedPrefixWord old (initializeCardinalityLow price (tickLogTick tick)) 216 := by
  unfold initializeCompiledCardinality
  rw [initializeCompiledTick_eq old price tick hp, u256_lor_comm, u256_land_comm]
  apply packedPrefixWord_masked old _ _ _ _ 184 32 (2 ^ 16) (by decide)
    (initializeTickLow_lt price _ hp) (by native_decide) (by native_decide) (by decide)
  rw [initializeCardinalityLow, packedAppend_toNat _ _ 200 16 (by decide)
    (lt_of_lt_of_le (initializeTickLow_lt price _ hp) (by decide))]
  rfl

theorem initializeCompiledNext_eq (old price tick : UInt256) (hp : price.toNat < 2 ^ 160) :
    initializeCompiledNext old price tick =
      packedPrefixWord old (initializeNextLow price (tickLogTick tick)) 232 := by
  unfold initializeCompiledNext
  rw [initializeCompiledCardinality_eq old price tick hp, u256_lor_comm, u256_land_comm]
  apply packedPrefixWord_masked old _ _ _ _ 216 16 1 (by decide)
    (initializeCardinalityLow_lt price _ hp) (by native_decide) (by native_decide) (by decide)
  rw [initializeNextLow, packedAppend_toNat _ _ 216 16 (by decide)
    (initializeCardinalityLow_lt price _ hp)]
  rfl

theorem initializeCompiledWord_eq (old price tick : UInt256) (hp : price.toNat < 2 ^ 160) :
    initializeCompiledWord old price tick = initializeSlot0Word old price (tickLogTick tick) := by
  unfold initializeCompiledWord initializeSlot0Word
  rw [initializeCompiledNext_eq old price tick hp, u256_land_comm]
  apply packedPrefixWord_masked old _ _ _ _ 232 16 (2 ^ 8) (by decide)
    (initializeNextLow_lt price _ hp) (by native_decide) (by native_decide) (by decide)
  rw [initializeUnlockedLow, packedAppend_toNat _ _ 240 8 (by decide)
    (lt_of_lt_of_le (initializeNextLow_lt price _ hp) (by decide))]
  rfl

end Benchmarks.UniswapV3.Pool
