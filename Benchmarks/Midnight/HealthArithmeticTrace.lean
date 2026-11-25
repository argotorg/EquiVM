import Benchmarks.Midnight.BitmapArithmetic
import Benchmarks.Midnight.PackedArray
import Benchmarks.Midnight.CheckedArithmeticRevert
import Benchmarks.Midnight.MulDivSource
import Benchmarks.Midnight.RuntimeBlocks_076

variable {fork : Ethereum.Fork}

/-! The two checked collateral-value products and the checked debt-capacity sum. -/

open Stele ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace Benchmarks.Midnight

def healthCollateralWord (load : UInt256 → UInt256) (base index : UInt256) : UInt256 :=
  low128 (UInt256.shiftRight (load (base + UInt256.ofNat (index.toNat / 2)))
    (UInt256.ofNat (128 * (index.toNat % 2))))

def healthPriceValue (collateral price : UInt256) : UInt256 :=
  mulDivDown collateral price (UInt256.ofNat 1000000000000000000000000000000000000)

def healthCollateralCapacity (collateral price lltv : UInt256) : UInt256 :=
  mulDivDown (healthPriceValue collateral price) lltv (UInt256.ofNat 1000000000000000000)

def HealthArithmeticSafe (collateral price lltv maxDebt : UInt256) : Prop :=
  collateral.toNat * price.toNat < UInt256.size ∧
  (healthPriceValue collateral price).toNat * lltv.toNat < UInt256.size ∧
  maxDebt.toNat + (healthCollateralCapacity collateral price lltv).toNat < UInt256.size

set_option maxRecDepth 2000000 in
theorem midnightHealthArithmetic {I : ExecutionEnv} {g : Sat256} {s0 : State}
    {mem rdata : ByteArray} {aw base index price cp bitmap maxDebt market lltv : UInt256}
    {σ : AccountMap} {k C : Nat} {R : List UInt256}
    (hstack : R.length + 22 ≤ 1024) (hi : index.toNat < 128)
    (hlltv : memLoad (cp + UInt256.ofNat 32) mem = lltv)
    (rd : RD fork midnightBytecode I g s0 ⟨19940⟩
      ([⟨20011⟩, base, index, price, cp, bitmap, maxDebt, base, market, index] ++ R)
      mem aw rdata σ k C) :
    let collateral := healthCollateralWord (fun slot ↦ solcSlotWordAt slot σ I) base index
    (¬ HealthArithmeticSafe collateral price lltv maxDebt ∧ RDrev fork midnightBytecode g s0) ∨
    (HealthArithmeticSafe collateral price lltv maxDebt ∧ ∃ aw' k' C',
      RD fork midnightBytecode I g s0 ⟨19847⟩
        ([base, market, bitmapClear bitmap index,
          maxDebt + healthCollateralCapacity collateral price lltv] ++ R)
        mem aw' rdata σ k' C') := by
  dsimp only
  change memLoad (cp + ⟨32⟩) mem = lltv at hlltv
  let collateral := healthCollateralWord (fun slot ↦ solcSlotWordAt slot σ I) base index
  have rd1 := midnightBlocks.midnight_block_19940
    (R := base :: market :: index :: R)
    (by simp only [List.length_cons]; omega) (by jump_dest) rd
  simp only [midnightBlocks.midnight_block_19940_stack, uint128Mask_computed] at rd1
  obtain ⟨k2, C2, rd2⟩ := midnightUint128ArrayLocation
    (by simp only [List.length_cons]; omega) hi (by jump_dest) rd1
  obtain ⟨k3, C3, rd3⟩ := midnightBlocks.midnight_block_7240
    (by simp only [List.length_cons]; omega) (by jump_dest) rd2
  simp only [midnightBlocks.midnight_block_7240_stack, (uint128ArrayIndexFacts index hi).2.2]
    at rd3
  change RD fork midnightBytecode I g s0 ⟨20413⟩
    (collateral :: price :: ⟨20001⟩ :: UInt256.ofNat 1000000000000000000000000000000000000 ::
      ⟨32⟩ :: cp :: ⟨20011⟩ :: UInt256.ofNat 1000000000000000000 :: maxDebt ::
      ⟨20018⟩ :: ⟨1⟩ :: bitmap :: UInt256.ofNat (2^128-1) :: base :: market :: index :: R)
    mem aw rdata σ k3 C3 at rd3
  by_cases hmul : collateral.toNat * price.toNat < UInt256.size
  · obtain ⟨k4, C4, rd4⟩ := midnightCheckedMul
      (by simp only [List.length_cons]; omega) hmul (by jump_dest) rd3
    have rd5 := midnightBlocks.midnight_block_20001
      (by simp only [List.length_cons]; omega) (by jump_dest) rd4
    simp only [midnightBlocks.midnight_block_20001_stack, hlltv] at rd5
    by_cases hmul2 : (healthPriceValue collateral price).toNat * lltv.toNat < UInt256.size
    · obtain ⟨k6, C6, rd6⟩ := midnightCheckedMul (ret := ⟨20011⟩)
        (by simp only [List.length_cons]; omega) hmul2 (by jump_dest) rd5
      have rd7 := midnightBlocks.midnight_block_20011
        (by simp only [List.length_cons]; omega) (by jump_dest) rd6
      simp only [midnightBlocks.midnight_block_20011_stack] at rd7
      by_cases hadd : maxDebt.toNat +
          (healthCollateralCapacity collateral price lltv).toNat < UInt256.size
      · obtain ⟨k8, C8, rd8⟩ := midnightCheckedAdd
          (by simp only [List.length_cons]; omega) hadd (by jump_dest) rd7
        have rd9 := midnightBlocks.midnight_block_20018
          (by omega) (by jump_dest) rd8
        simp only [midnightBlocks.midnight_block_20018_stack] at rd9
        have hclear : UInt256.land
            (UInt256.land (UInt256.lnot (UInt256.shiftLeft ⟨1⟩ index)) bitmap)
            (UInt256.ofNat (2^128-1)) = bitmapClear bitmap index := by
          rw [u256_land_comm (UInt256.lnot _)]
          rfl
        rw [hclear] at rd9
        exact Or.inr ⟨⟨hmul, hmul2, hadd⟩, _, _, _, rd9⟩
      · exact Or.inl ⟨fun h ↦ hadd h.2.2, midnightCheckedAddRevert
          (a := maxDebt) (b := healthCollateralCapacity collateral price lltv)
          (by simp only [List.length_cons]; omega) (by omega) rd7⟩
    · exact Or.inl ⟨fun h ↦ hmul2 h.2.1, midnightCheckedMulRevert
        (a := healthPriceValue collateral price) (b := lltv)
        (by simp only [List.length_cons]; omega) (by omega) rd5⟩
  · exact Or.inl ⟨fun h ↦ hmul h.1, midnightCheckedMulRevert
      (by simp only [List.length_cons]; omega) (by omega) rd3⟩

end Benchmarks.Midnight
