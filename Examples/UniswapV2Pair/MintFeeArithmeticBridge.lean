import Examples.UniswapV2Pair.MintFeeRoutinesCore

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem mintFeeRootDiffWord_eq_sub
    (rootK rootKLast : Int)
    (hroot : rootK > rootKLast)
    (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast) :
    mintFeeRootDiffWord rootK rootKLast =
      UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat) := by
  apply u256_inj
  have hlastLe : rootKLast.toNat ≤ rootK.toNat :=
    Int.toNat_le_toNat (by omega)
  have hlastSize : rootKLast.toNat < UInt256.size := lt_of_le_of_lt hlastLe hrootKSize
  have hdiffLe : (rootK - rootKLast).toNat ≤ rootK.toNat :=
    Int.toNat_le_toNat (by omega)
  have hdiffSize : (rootK - rootKLast).toNat < UInt256.size :=
    lt_of_le_of_lt hdiffLe hrootKSize
  rw [mintFeeRootDiffWord, ulit_toNat' _ hdiffSize]
  rw [usub_toNat (a := UInt256.ofNat rootK.toNat)
    (b := UInt256.ofNat rootKLast.toNat)]
  · rw [ulit_toNat' _ hrootKSize, ulit_toNat' _ hlastSize]
    rw [← Int.toNat_sub rootK.toNat rootKLast.toNat]
    congr 1
    simp [Int.toNat_of_nonneg hrootKNonneg, Int.toNat_of_nonneg hrootKLastNonneg]
  · rw [ulit_toNat' _ hrootKSize, ulit_toNat' _ hlastSize]
    exact hlastLe

theorem mintFeeRootTimesFiveWord_eq_mul
    (rootK : Int)
    (hfit : mintFeeRootTimesFiveNat rootK < UInt256.size) :
    mintFeeRootTimesFiveWord rootK =
      UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) := by
  apply u256_inj
  have hrootKSize : rootK.toNat < UInt256.size := by
    have hle : rootK.toNat ≤ rootK.toNat * 5 := by nlinarith
    exact lt_of_le_of_lt hle (by simpa [mintFeeRootTimesFiveNat] using hfit)
  rw [mintFeeRootTimesFiveWord, ulit_toNat' _ hfit]
  rw [u256_mul_toNat, ulit_toNat' _ hrootKSize,
    show (⟨5⟩ : UInt256).toNat = 5 from by decide]
  rw [Nat.mod_eq_of_lt (by simpa [mintFeeRootTimesFiveNat] using hfit)]
  rfl

theorem mintFeeDenominatorWord_eq_add
    (rootK rootKLast : Int)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size) :
    mintFeeDenominatorWord rootK rootKLast =
      mintFeeRootTimesFiveWord rootK + UInt256.ofNat rootKLast.toNat := by
  apply u256_inj
  have hrootKLastSize : rootKLast.toNat < UInt256.size := by
    have hle : rootKLast.toNat ≤ mintFeeDenominatorNat rootK rootKLast := by
      simp [mintFeeDenominatorNat]
    exact lt_of_le_of_lt hle hdenFit
  have hsumFit :
      (mintFeeRootTimesFiveWord rootK).toNat + rootKLast.toNat < UInt256.size := by
    simpa [mintFeeDenominatorNat] using hdenFit
  rw [mintFeeDenominatorWord, ulit_toNat' _ hdenFit]
  rw [uadd_toNat, ulit_toNat' _ hrootKLastSize]
  rw [Nat.mod_eq_of_lt hsumFit]
  rfl

theorem mintFeeDenominatorWord_eq_runtime_add
    (rootK rootKLast : Int)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size) :
    mintFeeDenominatorWord rootK rootKLast =
      UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
        UInt256.ofNat rootKLast.toNat := by
  rw [mintFeeDenominatorWord_eq_add rootK rootKLast hdenFit,
    mintFeeRootTimesFiveWord_eq_mul rootK hrootFiveFit]

theorem mintFeeNumeratorWord_eq_mul
    (evm : EVM.State) (rootK rootKLast : Int)
    (hfit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size) :
    mintFeeNumeratorWord evm rootK rootKLast =
      UInt256.mul (mintFunctionTotalSupplyWord evm) (mintFeeRootDiffWord rootK rootKLast) := by
  apply u256_inj
  have hprodFit :
      (mintFunctionTotalSupplyWord evm).toNat *
          (mintFeeRootDiffWord rootK rootKLast).toNat <
        UInt256.size := by
    simpa [mintFeeNumeratorNat] using hfit
  rw [mintFeeNumeratorWord, ulit_toNat' _ hfit]
  rw [u256_mul_toNat, Nat.mod_eq_of_lt hprodFit]
  rfl

theorem mintFeeNumeratorWord_eq_runtime_mul
    (evm : EVM.State) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast)
    (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast)
    (hfit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size) :
    mintFeeNumeratorWord evm rootK rootKLast =
      UInt256.mul (mintFunctionTotalSupplyWord evm)
        (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)) := by
  rw [mintFeeNumeratorWord_eq_mul evm rootK rootKLast hfit,
    mintFeeRootDiffWord_eq_sub rootK rootKLast hroot hrootKNonneg hrootKSize
      hrootKLastNonneg]

theorem mintFeeLiquidityInt_nonneg (evm : EVM.State) (rootK rootKLast : Int) :
    0 ≤ mintFeeLiquidityInt evm rootK rootKLast := by
  unfold mintFeeLiquidityInt
  exact Int.ediv_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)

theorem mintFeeLiquidityInt_not_pos_of_totalSupply_zero
    (evm : EVM.State) (rootK rootKLast : Int)
    (htotal : mintFunctionTotalSupplyWord evm = ⟨0⟩) :
    ¬ mintFeeLiquidityInt evm rootK rootKLast > 0 := by
  have hnumNat : mintFeeNumeratorNat evm rootK rootKLast = 0 := by
    simp [mintFeeNumeratorNat, htotal]
  have hnumWord : mintFeeNumeratorWord evm rootK rootKLast = ⟨0⟩ := by
    rw [mintFeeNumeratorWord, hnumNat]
    decide +native
  have hnumToNat : (mintFeeNumeratorWord evm rootK rootKLast).toNat = 0 := by
    rw [hnumWord]
    rfl
  unfold mintFeeLiquidityInt
  rw [hnumToNat]
  norm_num

theorem mintFeeLiquidityWord_eq_div
    (evm : EVM.State) (rootK rootKLast : Int)
    (hliqFit : (mintFeeLiquidityInt evm rootK rootKLast).toNat < UInt256.size) :
    mintFeeLiquidityWord evm rootK rootKLast =
      UInt256.div (mintFeeNumeratorWord evm rootK rootKLast)
        (mintFeeDenominatorWord rootK rootKLast) := by
  apply u256_inj
  rw [mintFeeLiquidityWord, ulit_toNat' _ hliqFit]
  rw [udiv_toNat]
  unfold mintFeeLiquidityInt
  let m := (mintFeeNumeratorWord evm rootK rootKLast).toNat
  let n := (mintFeeDenominatorWord rootK rootKLast).toNat
  change ((m : Int) / (n : Int)).toNat = m / n
  have hcast : ((m / n : Nat) : Int) = (m : Int) / (n : Int) := Int.natCast_ediv m n
  exact (congrArg Int.toNat hcast.symm).trans (Int.toNat_natCast (m / n))

theorem mintFeeLiquidityWord_eq_runtime_div
    (evm : EVM.State) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast)
    (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hliqFit : (mintFeeLiquidityInt evm rootK rootKLast).toNat < UInt256.size) :
    mintFeeLiquidityWord evm rootK rootKLast =
      UInt256.div
        (UInt256.mul (mintFunctionTotalSupplyWord evm)
          (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)))
        (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
          UInt256.ofNat rootKLast.toNat) := by
  rw [mintFeeLiquidityWord_eq_div evm rootK rootKLast hliqFit,
    mintFeeNumeratorWord_eq_runtime_mul evm rootK rootKLast hroot hrootKNonneg hrootKSize
      hrootKLastNonneg hnumFit,
    mintFeeDenominatorWord_eq_runtime_add rootK rootKLast hrootFiveFit hdenFit]

theorem mintFeeRuntimeRootGt_of_int_gt
    (rootK rootKLast : Int)
    (hroot : rootK > rootKLast)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast) :
    (UInt256.ofNat rootKLast.toNat).toNat < (UInt256.ofNat rootK.toNat).toNat := by
  have hrootKPos : 0 < rootK := by omega
  have hlastSize : rootKLast.toNat < UInt256.size := by
    have hlastLe : rootKLast.toNat ≤ rootK.toNat :=
      Int.toNat_le_toNat (by omega)
    exact lt_of_le_of_lt hlastLe hrootKSize
  rw [ulit_toNat' _ hlastSize, ulit_toNat' _ hrootKSize]
  exact (Int.toNat_lt_toNat hrootKPos).mpr hroot

theorem mintFeeRuntimeRootLe_of_int_not_gt
    (rootK rootKLast : Int)
    (hroot : ¬ rootK > rootKLast)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastSize : rootKLast.toNat < UInt256.size) :
    (UInt256.ofNat rootK.toNat).toNat ≤ (UInt256.ofNat rootKLast.toNat).toNat := by
  rw [ulit_toNat' _ hrootKSize, ulit_toNat' _ hrootKLastSize]
  exact Int.toNat_le_toNat (by omega)

theorem mintFeeRuntimeNumeratorFit
    (evm : EVM.State) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast)
    (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size) :
    (mintFunctionTotalSupplyWord evm).toNat *
        (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)).toNat <
      UInt256.size := by
  have hdiff :=
    congrArg UInt256.toNat
      (mintFeeRootDiffWord_eq_sub rootK rootKLast hroot hrootKNonneg hrootKSize
        hrootKLastNonneg)
  rw [← hdiff]
  simpa [mintFeeNumeratorNat] using hnumFit

theorem mintFeeRuntimeRootTimesFiveFit
    (rootK : Int)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size) :
    (UInt256.ofNat rootK.toNat).toNat * 5 < UInt256.size := by
  have hrootKSize : rootK.toNat < UInt256.size := by
    have hle : rootK.toNat ≤ rootK.toNat * 5 := by nlinarith
    exact lt_of_le_of_lt hle (by simpa [mintFeeRootTimesFiveNat] using hrootFiveFit)
  rw [ulit_toNat' _ hrootKSize]
  simpa [mintFeeRootTimesFiveNat] using hrootFiveFit

theorem mintFeeRuntimeDenominatorFit
    (rootK rootKLast : Int)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size) :
    (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256)).toNat +
        (UInt256.ofNat rootKLast.toNat).toNat <
      UInt256.size := by
  have hrootMul :=
    congrArg UInt256.toNat (mintFeeRootTimesFiveWord_eq_mul rootK hrootFiveFit)
  have hrootKLastSize : rootKLast.toNat < UInt256.size := by
    have hle : rootKLast.toNat ≤ mintFeeDenominatorNat rootK rootKLast := by
      simp [mintFeeDenominatorNat]
    exact lt_of_le_of_lt hle hdenFit
  rw [← hrootMul, ulit_toNat' _ hrootKLastSize]
  simpa [mintFeeDenominatorNat] using hdenFit

theorem mintFeeRuntimeDenominator_ne_zero
    (rootK rootKLast : Int)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0) :
    UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
        UInt256.ofNat rootKLast.toNat ≠
      ⟨0⟩ := by
  intro hzero
  apply hdenom
  have hdenEq :=
    mintFeeDenominatorWord_eq_runtime_add rootK rootKLast hrootFiveFit hdenFit
  rw [hdenEq, hzero]
  rfl

theorem mintFeeLiquidityWord_eq_zero_of_not_pos
    (evm : EVM.State) (rootK rootKLast : Int)
    (hliq : ¬ mintFeeLiquidityInt evm rootK rootKLast > 0) :
    mintFeeLiquidityWord evm rootK rootKLast = ⟨0⟩ := by
  have hnonneg := mintFeeLiquidityInt_nonneg evm rootK rootKLast
  have hzero : mintFeeLiquidityInt evm rootK rootKLast = 0 := by omega
  apply u256_inj
  rw [mintFeeLiquidityWord, hzero]
  change (UInt256.ofNat 0).toNat = (⟨0⟩ : UInt256).toNat
  rw [ulit_toNat' 0 (by norm_num [UInt256.size])]
  rfl

theorem mintFeeLiquidityWord_ne_zero_of_pos
    (evm : EVM.State) (rootK rootKLast : Int)
    (hliq : mintFeeLiquidityInt evm rootK rootKLast > 0)
    (hliqFit : (mintFeeLiquidityInt evm rootK rootKLast).toNat < UInt256.size) :
    mintFeeLiquidityWord evm rootK rootKLast ≠ ⟨0⟩ := by
  intro hzero
  have htoNat := congrArg UInt256.toNat hzero
  rw [mintFeeLiquidityWord, ulit_toNat' _ hliqFit] at htoNat
  have htoNatZero : (mintFeeLiquidityInt evm rootK rootKLast).toNat = 0 := by
    simpa using htoNat
  have hnonpos : mintFeeLiquidityInt evm rootK rootKLast ≤ 0 := by
    exact Int.toNat_eq_zero.mp htoNatZero
  omega

end UniswapV2Pair
