import Benchmarks.Midnight.LiquidateMaxRepaid
import Benchmarks.Midnight.CheckedAddGas
import Benchmarks.Midnight.CheckedExtraGas
import Benchmarks.Midnight.RuntimeBlocks_028
import Benchmarks.Midnight.RuntimeBlocks_027

variable {fork : Ethereum.Fork}

/-! The maximum-repayment ratio, including denominator underflow and division by zero. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

set_option maxRecDepth 10000

theorem midnightLiquidateRcfQuotient {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw product shortfall : UInt256} {σ : AccountMap} {k C : Nat}
    {R : List UInt256} (hstack : R.length + 8 ≤ 1024) (hx : shortfall.toNat < 2 ^ 128)
    (rd : RD fork midnightBytecode I g s0 ⟨7047⟩ (product :: shortfall :: R) mem aw rdata σ k C) :
    (¬ product.toNat < liquidatePriceScale.toNat ∧ RDrev fork midnightBytecode g s0) ∨
    (product.toNat < liquidatePriceScale.toNat ∧ ∃ k' C', C ≤ C' ∧
      RD fork midnightBytecode I g s0 ⟨7134⟩
        (mulDivUp shortfall liquidatePriceScale (UInt256.sub liquidatePriceScale product) :: R)
        mem aw rdata σ k' C') := by
  by_cases hle : product.toNat ≤ liquidatePriceScale.toNat
  · have hg : UInt256.gt (UInt256.sub liquidatePriceScale product) liquidatePriceScale = ⟨0⟩ :=
      ugt_zero (by rw [usub_toNat hle]; omega)
    have rd1 := midnightBlocks.midnight_block_7047_fallthrough
      (R := shortfall :: R) (by simp only [List.length_cons]; omega) hg rd
    simp only [midnightBlocks.midnight_block_7047_fallthrough_stack] at rd1
    have hm := liquidatePriceScale_mul_fit hx
    have hg2 : UInt256.isZero (UInt256.lor
        (UInt256.eq liquidatePriceScale (UInt256.div (UInt256.mul liquidatePriceScale shortfall) shortfall))
        (UInt256.isZero shortfall)) = ⟨0⟩ := by
      rw [uInt256_eq_comm liquidatePriceScale, u256_mul_comm liquidatePriceScale]
      exact checkedMulGuard hm
    have rd2 := midnightBlocks.midnight_block_7074_fallthrough (R := R) (by omega) hg2 rd1
    simp only [midnightBlocks.midnight_block_7074_fallthrough_stack] at rd2
    change RD fork midnightBytecode I g s0 ⟨7108⟩
      (UInt256.sub liquidatePriceScale product :: UInt256.mul liquidatePriceScale shortfall :: R)
      mem aw rdata σ _ _ at rd2
    rw [u256_mul_comm liquidatePriceScale shortfall] at rd2
    by_cases hlt : product.toNat < liquidatePriceScale.toNat
    · have hd : (UInt256.sub liquidatePriceScale product).toNat =
          liquidatePriceScale.toNat - product.toNat := usub_toNat hle
      have hp : 0 < (UInt256.sub liquidatePriceScale product).toNat := by rw [hd]; omega
      have hs := liquidateScaledRatioSafe hx hp (show
        (UInt256.sub liquidatePriceScale product).toNat ≤ liquidatePriceScale.toNat by rw [hd]; omega)
      have hg3 : UInt256.gt
          (UInt256.sub liquidatePriceScale product + UInt256.lnot ⟨0⟩)
          (UInt256.sub liquidatePriceScale product) = ⟨0⟩ := by
        rw [u256_add_lnot_zero_eq_sub_one]
        exact ugt_zero (by
          rw [usub_toNat (a := UInt256.sub liquidatePriceScale product) (b := ⟨1⟩) hp]
          omega)
      have rd3 := midnightBlocks.midnight_block_7108_fallthrough
        (by simp only [List.length_cons]; omega) hg3 rd2
      have rd4 := midnightBlocks.midnight_block_7118 (R := R) (by omega) (by jump_dest) rd3
      simp only [midnightBlocks.midnight_block_7118_stack, u256_add_lnot_zero_eq_sub_one] at rd4
      obtain ⟨k5, C5, hc5, rd5⟩ := midnightCheckedAdd_mono
        (by simp only [List.length_cons]; omega) hs.2.2 (by jump_dest) rd4
      have rd6 := midnightBlocks.midnight_block_6721
        (by simp only [List.length_cons]; omega) (by jump_dest) rd5
      have hnz : UInt256.sub liquidatePriceScale product ≠ ⟨0⟩ := by
        intro hz
        rw [hz] at hp
        exact Nat.lt_irrefl 0 hp
      obtain ⟨k7, C7, hc7, rd7⟩ := midnightCheckedDiv_mono (by omega) hnz (by jump_dest) rd6
      exact Or.inr ⟨hlt, k7, C7, by omega, rd7⟩
    · have he : product = liquidatePriceScale := u256_inj (by omega)
      have hz : UInt256.sub liquidatePriceScale product = ⟨0⟩ := by rw [he, u256_sub_self]
      have rr := midnightBlocks.midnight_block_7108_taken
        (by simp only [List.length_cons]; omega) (by rw [hz]; decide +kernel) (by jump_dest) rd2
      exact Or.inl ⟨hlt, midnightBlocks.midnight_block_7276
        (by simp only [List.length_cons]; omega) rr⟩
  · have hg : UInt256.gt (UInt256.sub liquidatePriceScale product) liquidatePriceScale = ⟨1⟩ := by
      apply ugt_one
      rw [usub_toNat_underflow (Nat.lt_of_not_ge hle)]
      have hp := product.val.isLt
      change product.toNat < UInt256.size at hp
      omega
    have rr := midnightBlocks.midnight_block_7047_taken
      (R := shortfall :: R) (by simp only [List.length_cons]; omega)
      (by change UInt256.gt (UInt256.sub liquidatePriceScale product) liquidatePriceScale ≠ ⟨0⟩
          rw [hg]; decide) (by jump_dest) rd
    exact Or.inl ⟨fun h ↦ hle (Nat.le_of_lt h), midnightBlocks.midnight_block_7276
      (by simp only [midnightBlocks.midnight_block_7047_taken_stack, List.length_cons]; omega) rr⟩

end Benchmarks.Midnight
