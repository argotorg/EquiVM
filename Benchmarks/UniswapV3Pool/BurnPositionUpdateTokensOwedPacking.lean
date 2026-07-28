import Benchmarks.UniswapV3Pool.BurnPositionUpdateSourceSuccess
import Benchmarks.UniswapV3Pool.BurnPositionUpdatePostReturn

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem burnWordSubInt_ofNat_toNat_eq (a b : UInt256) :
    burnWordSubInt (Int.ofNat a.toNat) (Int.ofNat b.toNat) =
      Int.ofNat (UInt256.sub a b).toNat := by
  unfold burnWordSubInt
  by_cases hle : b.toNat ≤ a.toNat
  · rw [usub_toNat (a := a) (b := b) hle]
    have hnonneg : 0 ≤ (a.toNat : Int) - (b.toNat : Int) := by omega
    have hlt : (a.toNat : Int) - (b.toNat : Int) < (2 ^ 256 : Int) := by
      have ha : a.toNat < UInt256.size := a.val.isLt
      norm_num [UInt256.size] at ha ⊢
      omega
    change ((a.toNat : Int) - (b.toNat : Int)) % (2 ^ 256 : Int) =
      Int.ofNat (a.toNat - b.toNat)
    rw [Int.emod_eq_of_lt hnonneg hlt]
    norm_num
    omega
  · have hltab : a.toNat < b.toNat := Nat.lt_of_not_ge hle
    rw [usub_toNat_underflow (a := a) (b := b) hltab]
    have ha : a.toNat < UInt256.size := a.val.isLt
    have hb : b.toNat < UInt256.size := b.val.isLt
    have hwrappedNonneg : 0 ≤ (UInt256.size + a.toNat - b.toNat : Int) := by
      norm_num [UInt256.size] at ha hb ⊢
      omega
    have hwrappedLt : (UInt256.size + a.toNat - b.toNat : Int) < (2 ^ 256 : Int) := by
      norm_num [UInt256.size] at ha hb ⊢
      omega
    have hdiff :
        (a.toNat : Int) - (b.toNat : Int) =
          (UInt256.size + a.toNat - b.toNat : Int) + (-1 : Int) * (2 ^ 256 : Int) := by
      norm_num [UInt256.size] at ha hb ⊢
      omega
    change ((a.toNat : Int) - (b.toNat : Int)) % (2 ^ 256 : Int) =
      Int.ofNat (UInt256.size + a.toNat - b.toNat)
    rw [hdiff]
    rw [Int.add_mul_emod_self_right]
    rw [Int.emod_eq_of_lt hwrappedNonneg hwrappedLt]
    norm_num [UInt256.size] at ha hb ⊢
    omega

theorem burnFullMathProd0Div128Mask_toNat (a b : UInt256) :
    (UInt256.land burnPositionUpdateSlot0Mask
      (UInt256.div (uniswapV3PoolFullMathMulDivProd0 a b)
        (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))).toNat =
      (a.toNat * b.toNat / 2 ^ 128) % 2 ^ 128 := by
  rw [burnPositionUpdateSlot0Mask_eq_uint128Mask]
  rw [u256_land_toNat, uint128Mask_toNat]
  rw [nat_land_comm]
  rw [nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128))
      (by norm_num [UInt256.size]))]
  rw [udiv_toNat]
  rw [show (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩).toNat = 2 ^ 128 by
    native_decide]
  rw [uniswapV3PoolFullMathMulDivProd0, u256_mul_toNat]
  rw [show UInt256.size = 2 ^ 256 by rfl]
  rw [show ((b.toNat * a.toNat % 2 ^ 256) / 2 ^ 128) % 2 ^ 128 =
      (b.toNat * a.toNat / 2 ^ 128) % 2 ^ 128 by omega]
  rw [Nat.mul_comm]

theorem burnPositionUpdateSourceTokensOwed0Int_eq_maskedWord
    (σ : AccountMap) (I : ExecutionEnv) (feeGrowthInside0X128 : UInt256) :
    burnPositionUpdateSourceTokensOwed0Int σ I (Int.ofNat feeGrowthInside0X128.toNat) =
      Int.ofNat
        (UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside0X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))).toNat := by
  rw [burnFullMathProd0Div128Mask_toNat]
  unfold burnPositionUpdateSourceTokensOwed0Int
  rw [burnWordSubInt_ofNat_toNat_eq]
  simp only [burnPositionUpdateSourceLiquidityInt]
  norm_num

theorem burnPositionUpdateSourceTokensOwed1Int_eq_maskedWord
    (σ : AccountMap) (I : ExecutionEnv) (feeGrowthInside1X128 : UInt256) :
    burnPositionUpdateSourceTokensOwed1Int σ I (Int.ofNat feeGrowthInside1X128.toNat) =
      Int.ofNat
        (UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside1X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))).toNat := by
  rw [burnFullMathProd0Div128Mask_toNat]
  unfold burnPositionUpdateSourceTokensOwed1Int
  rw [burnWordSubInt_ofNat_toNat_eq]
  simp only [burnPositionUpdateSourceLiquidityInt]
  norm_num

theorem burnPositionUpdateSourceTokensOwed0Int_eq_zero_of_mask_eq_zero
    {σ : AccountMap} {I : ExecutionEnv} {feeGrowthInside0X128 : UInt256}
    (h :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside0X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) = ⟨0⟩) :
    burnPositionUpdateSourceTokensOwed0Int σ I (Int.ofNat feeGrowthInside0X128.toNat) = 0 := by
  rw [burnPositionUpdateSourceTokensOwed0Int_eq_maskedWord]
  rw [h]
  rfl

theorem burnPositionUpdateSourceTokensOwed1Int_eq_zero_of_mask_eq_zero
    {σ : AccountMap} {I : ExecutionEnv} {feeGrowthInside1X128 : UInt256}
    (h :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside1X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) = ⟨0⟩) :
    burnPositionUpdateSourceTokensOwed1Int σ I (Int.ofNat feeGrowthInside1X128.toNat) = 0 := by
  rw [burnPositionUpdateSourceTokensOwed1Int_eq_maskedWord]
  rw [h]
  rfl

theorem burnPositionUpdateSourceTokensOwed0Int_pos_of_mask_ne_zero
    {σ : AccountMap} {I : ExecutionEnv} {feeGrowthInside0X128 : UInt256}
    (h :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside0X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) ≠ ⟨0⟩) :
    0 < burnPositionUpdateSourceTokensOwed0Int σ I
      (Int.ofNat feeGrowthInside0X128.toNat) := by
  rw [burnPositionUpdateSourceTokensOwed0Int_eq_maskedWord]
  have hpos : 0 <
      (UInt256.land burnPositionUpdateSlot0Mask
        (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub feeGrowthInside0X128
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))).toNat :=
    Nat.pos_of_ne_zero (by
      intro hzero
      exact h (uint256_toNat_eq_zero hzero))
  exact (Nat.cast_pos (α := Int)).2 hpos

theorem burnPositionUpdateSourceTokensOwed1Int_pos_of_mask_ne_zero
    {σ : AccountMap} {I : ExecutionEnv} {feeGrowthInside1X128 : UInt256}
    (h :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside1X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) ≠ ⟨0⟩) :
    0 < burnPositionUpdateSourceTokensOwed1Int σ I
      (Int.ofNat feeGrowthInside1X128.toNat) := by
  rw [burnPositionUpdateSourceTokensOwed1Int_eq_maskedWord]
  have hpos : 0 <
      (UInt256.land burnPositionUpdateSlot0Mask
        (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub feeGrowthInside1X128
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))).toNat :=
    Nat.pos_of_ne_zero (by
      intro hzero
      exact h (uint256_toNat_eq_zero hzero))
  exact (Nat.cast_pos (α := Int)).2 hpos

theorem burnPositionUpdateSourceTokensOwed1Int_eq_zero_of_slow_mask_eq_zero
    {σ : AccountMap} {I : ExecutionEnv} {feeGrowthInside1X128 : UInt256}
    (h :
      UInt256.land burnPositionUpdateSlot0Mask
          (uniswapV3PoolFullMathMulDivSlowResult
            (uniswapV3PoolFullMathMulDivProd1
              (UInt256.sub feeGrowthInside1X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside1X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))))
            (UInt256.sub feeGrowthInside1X128
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))) =
        ⟨0⟩) :
    burnPositionUpdateSourceTokensOwed1Int σ I (Int.ofNat feeGrowthInside1X128.toNat) =
      0 := by
  let a := UInt256.sub feeGrowthInside1X128
    (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩))
  let b := burnPositionUpdateSlot0Packed
    (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))
  exact burnPositionUpdateSourceTokensOwed1Int_eq_zero_of_mask_eq_zero
    (σ := σ) (I := I) (feeGrowthInside1X128 := feeGrowthInside1X128)
    (by
      have hlow := uniswapV3PoolFullMathMulDivSlowResult_low128_eq_prod0Div128 a b
      rw [← hlow]
      simpa [a, b] using h)

theorem burnPositionUpdateSourceTokensOwed1Int_pos_of_slow_mask_ne_zero
    {σ : AccountMap} {I : ExecutionEnv} {feeGrowthInside1X128 : UInt256}
    (h :
      UInt256.land burnPositionUpdateSlot0Mask
          (uniswapV3PoolFullMathMulDivSlowResult
            (uniswapV3PoolFullMathMulDivProd1
              (UInt256.sub feeGrowthInside1X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside1X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))))
            (UInt256.sub feeGrowthInside1X128
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))) ≠
        ⟨0⟩) :
    0 < burnPositionUpdateSourceTokensOwed1Int σ I
      (Int.ofNat feeGrowthInside1X128.toNat) := by
  let a := UInt256.sub feeGrowthInside1X128
    (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩))
  let b := burnPositionUpdateSlot0Packed
    (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))
  exact burnPositionUpdateSourceTokensOwed1Int_pos_of_mask_ne_zero
    (σ := σ) (I := I) (feeGrowthInside1X128 := feeGrowthInside1X128)
    (by
      have hlow := uniswapV3PoolFullMathMulDivSlowResult_low128_eq_prod0Div128 a b
      intro hzero
      exact h (by
        rw [hlow]
        simpa [a, b] using hzero))

private theorem burnPositionUpdateLandMaskAddLow_toNat (a b : UInt256) :
    (UInt256.land uint128Mask (a + UInt256.land uint128Mask b)).toNat =
      (a.toNat + b.toNat % 2 ^ 128) % 2 ^ 128 := by
  rw [u256_land_comm]
  rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
  rw [uadd_toNat]
  have hlowB : (UInt256.land uint128Mask b).toNat = b.toNat % 2 ^ 128 := by
    rw [u256_land_comm]
    rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt (by
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128))
        (by norm_num [UInt256.size]))]
  rw [hlowB]
  have hdiv : 2 ^ 128 ∣ UInt256.size := by
    change 2 ^ 128 ∣ 2 ^ 256
    exact Nat.pow_dvd_pow 2 (by omega)
  rw [Nat.mod_mod_of_dvd _ hdiv]
  rw [Nat.add_mod]
  rw [Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128))
      (by norm_num [UInt256.size]))]

private theorem burnPositionUpdateMaskedWordOfIntAdd_eq_landMaskAdd
    (base token : UInt256) :
    UInt256.land
        (EVM.wordOfInt
          (Int.ofNat (UInt256.land base uint128Mask).toNat +
            Int.ofNat (UInt256.land burnPositionUpdateSlot0Mask token).toNat))
        uint128Mask =
      UInt256.land burnPositionUpdateSlot0Mask
        (token + UInt256.land burnPositionUpdateSlot0Mask base) := by
  apply u256_inj
  rw [burnPositionUpdateSlot0Mask_eq_uint128Mask]
  rw [show EVM.wordOfInt
        (Int.ofNat (UInt256.land base uint128Mask).toNat +
          Int.ofNat (UInt256.land uint128Mask token).toNat) =
      UInt256.ofNat ((UInt256.land base uint128Mask).toNat +
        (UInt256.land uint128Mask token).toNat) by
    rw [wordOfInt_nonneg _ (by
      exact Int.add_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _))]
    rfl]
  rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
  rw [ulit_toNat' _ (by
    have h0 := uint128Mask_bound base
    have h1 := uint128Mask_bound token
    rw [u256_land_comm] at h1
    have h0le : (UInt256.land base uint128Mask).toNat ≤ 2 ^ 128 - 1 :=
      Nat.le_pred_of_lt h0
    have h1le : (UInt256.land uint128Mask token).toNat ≤ 2 ^ 128 - 1 :=
      Nat.le_pred_of_lt h1
    have hsum := Nat.add_le_add h0le h1le
    have hmax : (2 ^ 128 - 1) + (2 ^ 128 - 1) < UInt256.size := by
      norm_num [UInt256.size]
    exact lt_of_le_of_lt hsum hmax)]
  rw [Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128))
      (by norm_num [UInt256.size]))]
  rw [show (UInt256.land base uint128Mask).toNat = base.toNat % 2 ^ 128 by
    rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt (by
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128))
        (by norm_num [UInt256.size]))]]
  rw [show (UInt256.land uint128Mask token).toNat = token.toNat % 2 ^ 128 by
    rw [u256_land_comm]
    rw [u256_land_toNat, uint128Mask_toNat, nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt (by
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128))
        (by norm_num [UInt256.size]))]]
  rw [burnPositionUpdateLandMaskAddLow_toNat]
  omega

private theorem burnPositionUpdateSourceTokensOwed0StoreWord_eq_addedSlot3Low
    (old token : UInt256) :
    UInt256.lor
        (UInt256.land
          (EVM.wordOfInt
            (Int.ofNat (UInt256.land old uint128Mask).toNat +
              Int.ofNat (UInt256.land burnPositionUpdateSlot0Mask token).toNat))
          uint128Mask)
        (UInt256.land (UInt256.lnot uint128Mask) old) =
      burnPositionUpdateTokensOwed0AddedSlot3 old token := by
  rw [burnPositionUpdateMaskedWordOfIntAdd_eq_landMaskAdd]
  unfold burnPositionUpdateTokensOwed0AddedSlot3
  rw [burnPositionUpdateSlot0Mask_eq_uint128Mask]
  rw [u256_land_comm old (UInt256.lnot uint128Mask)]

private theorem burnPositionUpdateSourceTokensOwed1StoreWord_eq_addedSlot3High
    (old token : UInt256) :
    UInt256.lor
        (UInt256.mul
          (UInt256.land
            (EVM.wordOfInt
              (Int.ofNat (UInt256.land (UInt256.div old
                    (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) uint128Mask).toNat +
                Int.ofNat (UInt256.land burnPositionUpdateSlot0Mask token).toNat))
            uint128Mask)
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
        (UInt256.land old uint128Mask) =
      UInt256.lor
        (UInt256.mul
          (UInt256.land burnPositionUpdateSlot0Mask
            (token + UInt256.land burnPositionUpdateSlot0Mask
              (UInt256.div old (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
        (UInt256.land burnPositionUpdateSlot0Mask old) := by
  rw [burnPositionUpdateMaskedWordOfIntAdd_eq_landMaskAdd]
  rw [burnPositionUpdateSlot0Mask_eq_uint128Mask]
  rw [u256_land_comm uint128Mask old]

set_option maxHeartbeats 1000000 in
theorem burnPositionUpdateSourceTokensOwedFinalStoreWord_eq_addedSlot3
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hload :
      Solm.EVM.storageLoad
          (burnPositionUpdateSourceAfterTokensOwed0State evm σ I feeGrowthInside0X128)
          (burnPositionUpdateSourceAfterTokensOwed0State evm σ I
            feeGrowthInside0X128).executionEnv.codeOwner
          (burnPositionUpdateSourceTokensOwedSlot I) =
        burnPositionUpdateSourceTokensOwed0StoreWord evm σ I feeGrowthInside0X128) :
    burnPositionUpdateSourceTokensOwed1StoreWord
        (burnPositionUpdateSourceAfterTokensOwed0State evm σ I feeGrowthInside0X128)
        σ I feeGrowthInside1X128 =
      burnPositionUpdateTokensOwedAddedSlot3
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (burnPositionUpdateSourceTokensOwedSlot I))
        (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub feeGrowthInside0X128
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩))
        (UInt256.div
          (uniswapV3PoolFullMathMulDivProd0
            (UInt256.sub feeGrowthInside1X128
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
            (burnPositionUpdateSlot0Packed
              (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
          (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) := by
  let old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
    (burnPositionUpdateSourceTokensOwedSlot I)
  let token0 := UInt256.div
    (uniswapV3PoolFullMathMulDivProd0
      (UInt256.sub feeGrowthInside0X128
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)))
      (burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
    (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
  let token1 := UInt256.div
    (uniswapV3PoolFullMathMulDivProd0
      (UInt256.sub feeGrowthInside1X128
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
      (burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
    (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
  have hword0 :
      burnPositionUpdateSourceTokensOwed0StoreWord evm σ I feeGrowthInside0X128 =
        burnPositionUpdateTokensOwed0AddedSlot3 old token0 := by
    unfold burnPositionUpdateSourceTokensOwed0StoreWord
    unfold burnPositionUpdateSourceTokensOwed0WriteInt
    unfold burnPositionUpdateSourceStoredTokensOwed0Int
    rw [burnPositionUpdateSourceTokensOwed0Int_eq_maskedWord]
    simpa [old, token0] using
      burnPositionUpdateSourceTokensOwed0StoreWord_eq_addedSlot3Low old token0
  unfold burnPositionUpdateSourceTokensOwed1StoreWord
  unfold burnPositionUpdateSourceTokensOwed1WriteInt
  unfold burnPositionUpdateSourceStoredTokensOwed1Int
  rw [hload]
  rw [hword0]
  rw [burnPositionUpdateSourceTokensOwed1Int_eq_maskedWord]
  simpa [old, token0, token1, burnPositionUpdateTokensOwedAddedSlot3] using
    burnPositionUpdateSourceTokensOwed1StoreWord_eq_addedSlot3High
      (burnPositionUpdateTokensOwed0AddedSlot3 old token0) token1

private theorem burnPositionUpdateLandMask_add_low_eq_of_low_eq
    {a a' b : UInt256}
    (h :
      UInt256.land burnPositionUpdateSlot0Mask a =
        UInt256.land burnPositionUpdateSlot0Mask a') :
    UInt256.land burnPositionUpdateSlot0Mask
        (a + UInt256.land burnPositionUpdateSlot0Mask b) =
      UInt256.land burnPositionUpdateSlot0Mask
        (a' + UInt256.land burnPositionUpdateSlot0Mask b) := by
  apply u256_inj
  rw [burnPositionUpdateSlot0Mask_eq_uint128Mask] at h ⊢
  rw [burnPositionUpdateLandMaskAddLow_toNat]
  rw [burnPositionUpdateLandMaskAddLow_toNat]
  have hmask (x : UInt256) :
      (UInt256.land uint128Mask x).toNat = x.toNat % 2 ^ 128 := by
    rw [u256_land_toNat, uint128Mask_toNat, nat_land_comm, nat_land_mask_eq_mod]
    rw [Nat.mod_eq_of_lt (by
      exact lt_trans (Nat.mod_lt _ (by norm_num : 0 < 2 ^ 128))
        (by norm_num [UInt256.size]))]
  have hlow := congrArg UInt256.toNat h
  rw [hmask a, hmask a'] at hlow
  rw [Nat.add_mod, Nat.add_mod]
  rw [hlow]
  simp [Nat.add_mod]

theorem burnPositionUpdateTokensOwed0AddedSlot3_eq_of_low128
    {old token0 token0' : UInt256}
    (h0 :
      UInt256.land burnPositionUpdateSlot0Mask token0 =
        UInt256.land burnPositionUpdateSlot0Mask token0') :
    burnPositionUpdateTokensOwed0AddedSlot3 old token0 =
      burnPositionUpdateTokensOwed0AddedSlot3 old token0' := by
  unfold burnPositionUpdateTokensOwed0AddedSlot3
  rw [burnPositionUpdateLandMask_add_low_eq_of_low_eq h0]

theorem burnPositionUpdateTokensOwedAddedSlot3_eq_of_low128
    {old token0 token0' token1 token1' : UInt256}
    (h0 :
      UInt256.land burnPositionUpdateSlot0Mask token0 =
        UInt256.land burnPositionUpdateSlot0Mask token0')
    (h1 :
      UInt256.land burnPositionUpdateSlot0Mask token1 =
        UInt256.land burnPositionUpdateSlot0Mask token1') :
    burnPositionUpdateTokensOwedAddedSlot3 old token0 token1 =
      burnPositionUpdateTokensOwedAddedSlot3 old token0' token1' := by
  have h0word := burnPositionUpdateTokensOwed0AddedSlot3_eq_of_low128
    (old := old) h0
  unfold burnPositionUpdateTokensOwedAddedSlot3
  rw [h0word]
  rw [burnPositionUpdateLandMask_add_low_eq_of_low_eq h1]

theorem burnPositionUpdateSourceTokensOwedFinalStoreWord_eq_addedSlot3_of_low128
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv)
    (feeGrowthInside0X128 feeGrowthInside1X128 tokensOwed0 tokensOwed1 : UInt256)
    (hload :
      Solm.EVM.storageLoad
          (burnPositionUpdateSourceAfterTokensOwed0State evm σ I feeGrowthInside0X128)
          (burnPositionUpdateSourceAfterTokensOwed0State evm σ I
            feeGrowthInside0X128).executionEnv.codeOwner
          (burnPositionUpdateSourceTokensOwedSlot I) =
        burnPositionUpdateSourceTokensOwed0StoreWord evm σ I feeGrowthInside0X128)
    (h0 :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside0X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed0)
    (h1 :
      UInt256.land burnPositionUpdateSlot0Mask
          (UInt256.div
            (uniswapV3PoolFullMathMulDivProd0
              (UInt256.sub feeGrowthInside1X128
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
              (burnPositionUpdateSlot0Packed
                (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) =
        UInt256.land burnPositionUpdateSlot0Mask tokensOwed1) :
    burnPositionUpdateSourceTokensOwed1StoreWord
        (burnPositionUpdateSourceAfterTokensOwed0State evm σ I feeGrowthInside0X128)
        σ I feeGrowthInside1X128 =
      burnPositionUpdateTokensOwedAddedSlot3
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (burnPositionUpdateSourceTokensOwedSlot I))
        tokensOwed0 tokensOwed1 := by
  let token0 := UInt256.div
    (uniswapV3PoolFullMathMulDivProd0
      (UInt256.sub feeGrowthInside0X128
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨1⟩)))
      (burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
    (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
  let token1 := UInt256.div
    (uniswapV3PoolFullMathMulDivProd0
      (UInt256.sub feeGrowthInside1X128
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I) + ⟨2⟩)))
      (burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I)))))
    (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)
  have hfast :=
    burnPositionUpdateSourceTokensOwedFinalStoreWord_eq_addedSlot3
      evm σ I feeGrowthInside0X128 feeGrowthInside1X128 hload
  rw [hfast]
  exact burnPositionUpdateTokensOwedAddedSlot3_eq_of_low128
    (old := Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
      (burnPositionUpdateSourceTokensOwedSlot I))
    (token0 := token0) (token0' := tokensOwed0)
    (token1 := token1) (token1' := tokensOwed1)
    (by simpa [token0] using h0) (by simpa [token1] using h1)

end Benchmarks.UniswapV3Pool
