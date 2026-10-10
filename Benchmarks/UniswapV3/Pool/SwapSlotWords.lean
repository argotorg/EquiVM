import Benchmarks.UniswapV3.Pool.SwapSlotStorage

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace Benchmarks.UniswapV3.Pool
set_option maxRecDepth 10000

theorem swapSlotPriceWord_evm (old price : UInt256) :
    swapSlotFieldWord old price false =
      UInt256.lor
        (UInt256.land price
          (UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
            (UInt256.ofNat 1)))
        (UInt256.land
          (UInt256.lnot (UInt256.ofNat 1461501637330902918203684832716283019655932542975))
          old) := by
  have hm : packedFieldMask 0 160 =
      UInt256.lnot (UInt256.ofNat 1461501637330902918203684832716283019655932542975) := by
    native_decide
  have hv : UInt256.ofNat (2 ^ 160 - 1) =
      UInt256.sub (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160))
        (UInt256.ofNat 1) := by native_decide
  simp only [swapSlotFieldWord, Bool.false_eq_true, ↓reduceIte, packedFieldUpdate,
    packedFieldValue, hm, hv, pow_zero]
  change UInt256.lor (UInt256.land old _) (UInt256.mul _ ⟨1⟩) = _
  rw [u256_lor_comm, u256_land_comm old]
  congr 1
  apply u256_inj
  rw [u256_mul_toNat]
  change (_ * 1) % UInt256.size = _
  rw [Nat.mul_one]
  exact Nat.mod_eq_of_lt (UInt256.land price _).val.isLt

theorem swapSlotTickWord_evm (old tick : UInt256) :
    swapSlotFieldWord old tick true =
      UInt256.lor
        (UInt256.mul (UInt256.land tick (UInt256.ofNat 16777215))
          (UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160)))
        (UInt256.land
          (UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 16777215) (UInt256.ofNat 160)))
          old) := by
  have hm : packedFieldMask 160 24 =
      UInt256.lnot (UInt256.shiftLeft (UInt256.ofNat 16777215) (UInt256.ofNat 160)) := by
    native_decide
  have hv : UInt256.ofNat (2 ^ 160) =
      UInt256.shiftLeft (UInt256.ofNat 1) (UInt256.ofNat 160) := by native_decide
  simp only [swapSlotFieldWord, ↓reduceIte, packedFieldUpdate, packedFieldValue, hm, hv,
    show UInt256.ofNat (2 ^ 24 - 1) = UInt256.ofNat 16777215 from rfl]
  rw [u256_lor_comm, u256_land_comm old]

theorem swapSlotObservationWord_comm (old value observation : UInt256)
    (tick cardinality : Bool) :
    slot0ObservationWord (swapSlotFieldWord old value tick) observation cardinality =
      swapSlotFieldWord (slot0ObservationWord old observation cardinality) value tick := by
  cases tick <;> cases cardinality <;> apply wordMaskedUpdate_comm
  all_goals
    apply wordMask_preserves_of_contains
    · apply packedFieldValue_mask <;> decide
    · native_decide

theorem swapSlotPriceTickWord_comm (old price tick : UInt256) :
    swapSlotFieldWord (swapSlotFieldWord old price false) tick true =
      swapSlotFieldWord (swapSlotFieldWord old tick true) price false := by
  apply wordMaskedUpdate_comm
  · exact wordMask_preserves_of_contains _ _ _
      (packedFieldValue_mask price 0 160 (by decide) (by decide)) (by native_decide)
  · exact wordMask_preserves_of_contains _ _ _
      (packedFieldValue_mask tick 160 24 (by decide) (by decide)) (by native_decide)

theorem swapSlotFieldsWord_reorder (old price tick index cardinality : UInt256) :
    swapSlotFieldsWord old price tick index cardinality =
      swapSlotFieldWord
        (swapSlotFieldWord
          (slot0ObservationWord (slot0ObservationWord old cardinality true) index false)
          tick true) price false := by
  unfold swapSlotFieldsWord
  rw [slot0ObservationWords_comm]
  simp only [swapSlotObservationWord_comm]
  exact swapSlotPriceTickWord_comm _ _ _

end Benchmarks.UniswapV3.Pool
