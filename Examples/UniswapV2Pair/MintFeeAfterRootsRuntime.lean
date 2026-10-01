import Examples.UniswapV2Pair.MintInternalMintRuntime
import Examples.UniswapV2Pair.MintFeeArithmeticBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeAfterRootsNoMintReturnOfInt
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rootK rootKLast : Int)
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (hroot : ¬ rootK > rootKLast)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastSize : rootKLast.toNat < UInt256.size) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  exact uniswapMintFeeRuntimeAfterRootsNoMintReturn rd7899
    (mintFeeRuntimeRootLe_of_int_not_gt rootK rootKLast hroot hrootKSize hrootKLastSize)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeAfterRootsPositiveNoLiquidityReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rootK rootKLast : Int)
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k C)
    (evmFeeS : EVM.State)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast)
    (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hfeeLiq : ¬ mintFeeLiquidityInt evmFeeS rootK rootKLast > 0) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      mem aw rdata (cAFee, σFee) k' C' := by
  have hrootGt :=
    mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg
  have hnumFitRuntime :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat *
          (UInt256.sub (UInt256.ofNat rootK.toNat)
            (UInt256.ofNat rootKLast.toNat)).toNat <
        UInt256.size := by
    have hfit :=
      mintFeeRuntimeNumeratorFit evmFeeS rootK rootKLast hroot hrootKNonneg
        hrootKSize hrootKLastNonneg hnumFit
    simpa [htotalEq] using hfit
  have hrootK5Fit :=
    mintFeeRuntimeRootTimesFiveFit rootK hrootFiveFit
  have hdenFitRuntime :=
    mintFeeRuntimeDenominatorFit rootK rootKLast hrootFiveFit hdenFit
  have hdenominatorNe :=
    mintFeeRuntimeDenominator_ne_zero rootK rootKLast hrootFiveFit hdenFit hdenom
  have hliqIntZero : mintFeeLiquidityInt evmFeeS rootK rootKLast = 0 := by
    have hnonneg := mintFeeLiquidityInt_nonneg evmFeeS rootK rootKLast
    omega
  have hliqFit : (mintFeeLiquidityInt evmFeeS rootK rootKLast).toNat < UInt256.size := by
    simp [hliqIntZero, UInt256.size]
  have hliqWordZero :=
    mintFeeLiquidityWord_eq_zero_of_not_pos evmFeeS rootK rootKLast hfeeLiq
  have hliqRuntimeEq :
      UInt256.div
          (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
            (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)))
          (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
            UInt256.ofNat rootKLast.toNat) =
        mintFeeLiquidityWord evmFeeS rootK rootKLast := by
    have hword :=
      mintFeeLiquidityWord_eq_runtime_div evmFeeS rootK rootKLast hroot hrootKNonneg
        hrootKSize hrootKLastNonneg hnumFit hrootFiveFit hdenFit hliqFit
    rw [← htotalEq]
    exact hword.symm
  have hliqZero :
      UInt256.div
          (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
            (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)))
          (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
            UInt256.ofNat rootKLast.toNat) =
        ⟨0⟩ := by
    exact hliqRuntimeEq.trans hliqWordZero
  exact
    uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityZeroReturn rd7899 hrootGt
      hnumFitRuntime hrootK5Fit hdenFitRuntime hdenominatorNe hliqZero

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimeAfterRootsPositiveWithLiquidityReturn
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {kLast feeTo amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rootK rootKLast : Int)
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast, feeTo, ⟨1⟩,
        reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (evmFeeS : EVM.State)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast)
    (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hfeeLiq : mintFeeLiquidityInt evmFeeS rootK rootKLast > 0)
    (hfeeLiqFit : (mintFeeLiquidityInt evmFeeS rootK rootKLast).toNat < UInt256.size)
    (hperm : I.perm = true)
    (htotalFit :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat +
          (mintFeeLiquidityWord evmFeeS rootK rootKLast).toNat <
        UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + mintFeeLiquidityWord evmFeeS rootK rootKLast))
        (uniswapInternalMintBalanceHashSlot feeTo mem)).toNat +
          (mintFeeLiquidityWord evmFeeS rootK rootKLast).toNat <
        UInt256.size)
    (hmload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem)).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintBalanceHashMem feeTo
            (uniswapInternalMintBalanceHashMem feeTo mem)).readWithPadding
              (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩)
    (hlogMload64 :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintLogMem (mintFeeLiquidityWord evmFeeS rootK rootKLast)
              (uniswapInternalMintBalanceHashMem feeTo
                (uniswapInternalMintBalanceHashMem feeTo mem))).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem (mintFeeLiquidityWord evmFeeS rootK rootKLast)
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem))).readWithPadding
                (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩) :
    ∃ k' C', RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord,
        ⟨861⟩, sel]
      (uniswapInternalMintLogMem (mintFeeLiquidityWord evmFeeS rootK rootKLast)
        (uniswapInternalMintBalanceHashMem feeTo
          (uniswapInternalMintBalanceHashMem feeTo mem)))
      feeToStaticcallActiveWords rdata
      (cAFee, sstoreAccountMap I.codeOwner
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + mintFeeLiquidityWord evmFeeS rootK rootKLast))
        (uniswapInternalMintBalanceHashSlot feeTo
          (uniswapInternalMintBalanceHashMem feeTo mem))
        (uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + mintFeeLiquidityWord evmFeeS rootK rootKLast))
          (uniswapInternalMintBalanceHashSlot feeTo mem) +
            mintFeeLiquidityWord evmFeeS rootK rootKLast)) k' C' := by
  have hrootGt :=
    mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg
  have hnumFitRuntime :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat *
          (UInt256.sub (UInt256.ofNat rootK.toNat)
            (UInt256.ofNat rootKLast.toNat)).toNat <
        UInt256.size := by
    have hfit :=
      mintFeeRuntimeNumeratorFit evmFeeS rootK rootKLast hroot hrootKNonneg
        hrootKSize hrootKLastNonneg hnumFit
    simpa [htotalEq] using hfit
  have hrootK5Fit :=
    mintFeeRuntimeRootTimesFiveFit rootK hrootFiveFit
  have hdenFitRuntime :=
    mintFeeRuntimeDenominatorFit rootK rootKLast hrootFiveFit hdenFit
  have hdenominatorNe :=
    mintFeeRuntimeDenominator_ne_zero rootK rootKLast hrootFiveFit hdenFit hdenom
  have hliqWordNonzero :=
    mintFeeLiquidityWord_ne_zero_of_pos evmFeeS rootK rootKLast hfeeLiq hfeeLiqFit
  have hliqRuntimeEq :
      UInt256.div
          (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
            (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)))
          (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
            UInt256.ofNat rootKLast.toNat) =
        mintFeeLiquidityWord evmFeeS rootK rootKLast := by
    have hword :=
      mintFeeLiquidityWord_eq_runtime_div evmFeeS rootK rootKLast hroot hrootKNonneg
        hrootKSize hrootKLastNonneg hnumFit hrootFiveFit hdenFit hfeeLiqFit
    rw [← htotalEq]
    exact hword.symm
  have hliqRuntimeNonzero :
      UInt256.div
          (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
            (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)))
          (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
            UInt256.ofNat rootKLast.toNat) ≠
        ⟨0⟩ := by
    simpa [hliqRuntimeEq] using hliqWordNonzero
  have htotalFitRuntime :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat +
          (UInt256.div
            (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
              (UInt256.sub (UInt256.ofNat rootK.toNat)
                (UInt256.ofNat rootKLast.toNat)))
            (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
              UInt256.ofNat rootKLast.toNat)).toNat <
        UInt256.size := by
    simpa [hliqRuntimeEq] using htotalFit
  have hbalanceFitRuntime :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I +
            UInt256.div
              (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
                (UInt256.sub (UInt256.ofNat rootK.toNat)
                  (UInt256.ofNat rootKLast.toNat)))
              (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
                UInt256.ofNat rootKLast.toNat)))
        (uniswapInternalMintBalanceHashSlot feeTo mem)).toNat +
          (UInt256.div
            (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
              (UInt256.sub (UInt256.ofNat rootK.toNat)
                (UInt256.ofNat rootKLast.toNat)))
            (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
              UInt256.ofNat rootKLast.toNat)).toNat <
        UInt256.size := by
    simpa [hliqRuntimeEq] using hbalanceFit
  have hlogMload64Runtime :
      (if (⟨64⟩ : UInt256).toNat ≥
            (uniswapInternalMintLogMem
              (UInt256.div
                (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
                  (UInt256.sub (UInt256.ofNat rootK.toNat)
                    (UInt256.ofNat rootKLast.toNat)))
                (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
                  UInt256.ofNat rootKLast.toNat))
              (uniswapInternalMintBalanceHashMem feeTo
                (uniswapInternalMintBalanceHashMem feeTo mem))).size then ⟨0⟩
       else UInt256.ofNat
        (fromByteArrayBigEndian
          ((uniswapInternalMintLogMem
            (UInt256.div
              (UInt256.mul (uniswapSlotWord ⟨0⟩ σFee I)
                (UInt256.sub (UInt256.ofNat rootK.toNat)
                  (UInt256.ofNat rootKLast.toNat)))
              (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256) +
                UInt256.ofNat rootKLast.toNat))
            (uniswapInternalMintBalanceHashMem feeTo
              (uniswapInternalMintBalanceHashMem feeTo mem))).readWithPadding
                (⟨64⟩ : UInt256).toNat 32))) =
        ⟨128⟩ := by
    simpa [hliqRuntimeEq] using hlogMload64
  have hrd :=
    uniswapMintFeeRuntimeAfterRootsPositiveComputedLiquidityMintReturn rd7899 hrootGt
      hnumFitRuntime hrootK5Fit hdenFitRuntime hdenominatorNe hliqRuntimeNonzero hperm
      htotalFitRuntime hbalanceFitRuntime hmload64 hlogMload64Runtime
  simpa [hliqRuntimeEq] using hrd

end UniswapV2Pair
