import Examples.UniswapV2Pair.MintInitialProductOverflow
import Examples.UniswapV2Pair.MintFeeArithmeticBridge

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
set_option maxRecDepth 2000000
namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveNumeratorOverflowRevertsOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State}
    {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (UInt256.ofNat rootKLast.toNat :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeTo :: ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hover : UInt256.size ≤ mintFeeNumeratorNat evmFeeS rootK rootKLast)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev uniswapV2PairBytecode g
      s0 := by
  have hrootGt :=
    mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg
  obtain ⟨_, _, rd6879⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSubEntryOfTail (hov := hov) rd7899 hrootGt
  obtain ⟨_, _, rd6780⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntryOfTail (hov := hov) rd6879 hrootGt
  have hoverRuntime :
      UInt256.size ≤
        (uniswapSlotWord ⟨0⟩ σFee I).toNat *
          (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)).toNat := by
    rw [← htotalEq]
    have hdiff :=
      congrArg UInt256.toNat
        (mintFeeRootDiffWord_eq_sub rootK rootKLast hroot hrootKNonneg hrootKSize
          hrootKLastNonneg)
    rw [← hdiff]
    simpa [mintFeeNumeratorNat] using hover
  exact RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164
    (a := uniswapSlotWord ⟨0⟩ σFee I)
    (b := UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat))
    rd6780 hoverRuntime hmem hread64
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveRootTimesFiveOverflowRevertsOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State}
    {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (UInt256.ofNat rootKLast.toNat :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeTo :: ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size)
    (hover : UInt256.size ≤ mintFeeRootTimesFiveNat rootK)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev uniswapV2PairBytecode g
      s0 := by
  have hrootGt :=
    mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg
  obtain ⟨_, _, rd6879⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSubEntryOfTail (hov := hov) rd7899 hrootGt
  obtain ⟨_, _, rd6780Num⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntryOfTail (hov := hov) rd6879 hrootGt
  have hnumFitRuntime :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat *
          (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)).toNat <
        UInt256.size := by
    rw [← htotalEq]
    exact mintFeeRuntimeNumeratorFit evmFeeS rootK rootKLast hroot hrootKNonneg
      hrootKSize hrootKLastNonneg hnumFit
  obtain ⟨_, _, rd7945⟩ :=
    uniswapMintFeeRuntimePositiveNumeratorEntryOfTail (hov := hov) rd6780Num hnumFitRuntime
  obtain ⟨_, _, rd6780Den⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorMulEntryOfTail (hov := hov) rd7945
  have hoverRuntime : UInt256.size ≤ (UInt256.ofNat rootK.toNat).toNat * 5 := by
    rw [ulit_toNat' _ hrootKSize]
    simpa [mintFeeRootTimesFiveNat] using hover
  exact RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164
    (a := UInt256.ofNat rootK.toNat) (b := (⟨5⟩ : UInt256)) rd6780Den
    hoverRuntime hmem hread64
    (by simp only [List.length_cons]; omega)

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeRuntimePositiveDenominatorOverflowRevertsOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State}
    {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int}
    {kLast feeTo reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (UInt256.ofNat rootKLast.toNat :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast :: feeTo :: ⟨1⟩ ::
        reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hrootKLastSize : rootKLast.toNat < UInt256.size)
    (hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hover : UInt256.size ≤ mintFeeDenominatorNat rootK rootKLast)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    RDrev uniswapV2PairBytecode g
      s0 := by
  have hrootGt :=
    mintFeeRuntimeRootGt_of_int_gt rootK rootKLast hroot hrootKSize hrootKLastNonneg
  obtain ⟨_, _, rd6879⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSubEntryOfTail (hov := hov) rd7899 hrootGt
  obtain ⟨_, _, rd6780Num⟩ :=
    uniswapMintFeeRuntimeAfterRootsPositiveSupplyMulEntryOfTail (hov := hov) rd6879 hrootGt
  have hnumFitRuntime :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat *
          (UInt256.sub (UInt256.ofNat rootK.toNat) (UInt256.ofNat rootKLast.toNat)).toNat <
        UInt256.size := by
    rw [← htotalEq]
    exact mintFeeRuntimeNumeratorFit evmFeeS rootK rootKLast hroot hrootKNonneg
      hrootKSize hrootKLastNonneg hnumFit
  obtain ⟨_, _, rd7945⟩ :=
    uniswapMintFeeRuntimePositiveNumeratorEntryOfTail (hov := hov) rd6780Num hnumFitRuntime
  obtain ⟨_, _, rd6780Den⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorMulEntryOfTail (hov := hov) rd7945
  have hrootFiveFitRuntime := mintFeeRuntimeRootTimesFiveFit rootK hrootFiveFit
  obtain ⟨_, _, rd7970⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorProductEntryOfTail (hov := hov) rd6780Den hrootFiveFitRuntime
  obtain ⟨_, _, rd8515⟩ :=
    uniswapMintFeeRuntimePositiveDenominatorAddEntryOfTail (hov := hov) rd7970
  have hoverRuntime :
      UInt256.size ≤
        (UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256)).toNat +
          (UInt256.ofNat rootKLast.toNat).toNat := by
    have hrootMul :=
      congrArg UInt256.toNat (mintFeeRootTimesFiveWord_eq_mul rootK hrootFiveFit)
    rw [← hrootMul, ulit_toNat' _ hrootKLastSize]
    simpa [mintFeeDenominatorNat] using hover
  exact RD.uniswapSafeMathAddOverflow_feeToStaticcall_size164
    (a := UInt256.mul (UInt256.ofNat rootK.toNat) (⟨5⟩ : UInt256))
    (b := UInt256.ofNat rootKLast.toNat) rd8515 hoverRuntime hmem hread64
    (by simp only [List.length_cons]; omega)

end UniswapV2Pair
