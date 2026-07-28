import Benchmarks.UniswapV3Pool.Common

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

def uint128Mask : UInt256 := UInt256.ofNat (2 ^ 128 - 1)

theorem uint128Mask_toNat :
    uint128Mask.toNat = 2 ^ 128 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem uint128Mask_bound (w : UInt256) :
    (UInt256.land w uint128Mask).toNat < EVM.twoPow 128 := by
  rw [uland_toNat]
  rw [uint128Mask_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [EVM.twoPow])

theorem uint128Mask_clean {w : UInt256} (hcanon : w.toNat < EVM.twoPow 128) :
    UInt256.land w uint128Mask = w := by
  apply u256_inj
  show Nat.land w.toNat uint128Mask.toNat % EVM.twoPow 256 = w.toNat
  rw [uint128Mask_toNat, nat_land_mask_eq_mod]
  rw [show EVM.twoPow 128 = 2 ^ 128 from rfl] at hcanon
  rw [Nat.mod_eq_of_lt hcanon]
  exact Nat.mod_eq_of_lt w.val.isLt

theorem uint128Mask_clean_left {w : UInt256} (hcanon : w.toNat < EVM.twoPow 128) :
    UInt256.land uint128Mask w = w := by
  rw [u256_land_comm uint128Mask w]
  exact uint128Mask_clean hcanon

theorem uint128ReturnEncodingMasked (w : UInt256) :
    encodeReturnValue? uint128
        (.int (Int.ofNat (UInt256.land w uint128Mask).toNat)) =
      some (UInt256.toByteArray (UInt256.land w uint128Mask)) := by
  have hword : EVM.word (UInt256.land w uint128Mask).toNat = UInt256.land w uint128Mask := by
    show UInt256.ofNat (UInt256.land w uint128Mask).toNat = UInt256.land w uint128Mask
    exact u256_ofNat_toNat _
  refine scalarReturnEncoding (t := (.int (.uint ⟨128, by decide⟩)))
    (w := UInt256.land w uint128Mask) rfl ?_ ?_
  · simp only [abiTupleHeadSize?, staticABIEncodedSize?, isDynamicABIType, bind, Option.bind]
    decide
  · simp [encodeABIValue?, encodeABIWord?, hword, uint128Mask_bound w]

theorem uint128PairReturnEncodingMasked (w0 w1 : UInt256) :
    encodeReturnValues? [uint128, uint128]
        [.int (Int.ofNat (UInt256.land w0 uint128Mask).toNat),
          .int (Int.ofNat (UInt256.land w1 uint128Mask).toNat)] =
      some (UInt256.toByteArray (UInt256.land w0 uint128Mask) ++
        UInt256.toByteArray (UInt256.land w1 uint128Mask)) := by
  let r0 := UInt256.land w0 uint128Mask
  let r1 := UInt256.land w1 uint128Mask
  have hword0 : EVM.word r0.toNat = r0 := by
    show UInt256.ofNat r0.toNat = r0
    exact u256_ofNat_toNat r0
  have hword1 : EVM.word r1.toNat = r1 := by
    show UInt256.ofNat r1.toNat = r1
    exact u256_ofNat_toNat r1
  have henc0 :
      encodeABIValue? uint128 (.int (Int.ofNat r0.toNat)) =
        some (EVM.Word.toBytesBE r0) := by
    simp [uint128, uint128Int, encodeABIValue?, encodeABIWord?, hword0,
      show r0.toNat < EVM.twoPow 128 from by simpa [r0] using uint128Mask_bound w0]
  have henc1 :
      encodeABIValue? uint128 (.int (Int.ofNat r1.toNat)) =
        some (EVM.Word.toBytesBE r1) := by
    simp [uint128, uint128Int, encodeABIValue?, encodeABIWord?, hword1,
      show r1.toNat < EVM.twoPow 128 from by simpa [r1] using uint128Mask_bound w1]
  have hhead : abiTupleHeadSize? [uint128, uint128] = some 64 := by
    native_decide
  have hdyn : isDynamicABIType uint128 = false := by
    native_decide
  change encodeReturnValues? [uint128, uint128]
      [.int (Int.ofNat r0.toNat), .int (Int.ofNat r1.toNat)] =
    some (UInt256.toByteArray r0 ++ UInt256.toByteArray r1)
  rw [toByteArray_eq_toBytesBE r0, toByteArray_eq_toBytesBE r1]
  simp only [encodeReturnValues?, encodeABIValues?, encodeABIValuesFrom?, hhead, henc0, henc1,
    hdyn, bind, Option.bind, Bool.false_eq_true, if_false, List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp [r0, r1]

end Benchmarks.UniswapV3Pool
