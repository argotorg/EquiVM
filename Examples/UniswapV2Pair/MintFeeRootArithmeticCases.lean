import Examples.UniswapV2Pair.MintFeeOnKLastNonzeroRevertCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

-- Split on the actual roots produced by the shared sqrt routine.
theorem uniswapMintFeeActualRootArithmeticCasesOfTail
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State} {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int} {feeTo : AccountAddress}
    {kLast feeToWord reserve0 reserve1 ret : UInt256} {R : List UInt256}
    (rd7899 : RD uniswapV2PairBytecode I g
      s0 ⟨7899⟩
      (UInt256.ofNat rootKLast.toNat :: ⟨0⟩ :: UInt256.ofNat rootK.toNat :: kLast ::
        feeToWord :: ⟨1⟩ :: reserve1 :: reserve0 :: ret :: R)
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hrootKLastSize : rootKLast.toNat < UInt256.size)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    (mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
      mintFeeRootTimesFiveNat rootK < UInt256.size ∧
      mintFeeDenominatorNat rootK rootKLast < UInt256.size) ∨
    (ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
      evmFeeS [mintFeeRootComparisonStmt] .reverted ∧
      RDrev uniswapV2PairBytecode g
        s0) := by
  by_cases hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size
  · by_cases hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size
    · by_cases hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size
      · exact Or.inl ⟨hnumFit, hrootFiveFit, hdenFit⟩
      · exact Or.inr
          ⟨uniswapMintFeeAfterRoots_positiveDenominatorOverflow evmFeeS reserve0 reserve1
              feeTo kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg
              hnumFit hrootFiveFit (Nat.le_of_not_lt hdenFit),
            uniswapMintFeeRuntimePositiveDenominatorOverflowRevertsOfTail (hov := hov) rd7899 htotalEq hroot
              hrootKNonneg hrootKSize hrootKLastNonneg hrootKLastSize hnumFit hrootFiveFit
              (Nat.le_of_not_lt hdenFit) hmem hread64⟩
    · exact Or.inr
        ⟨uniswapMintFeeAfterRoots_positiveRootTimesFiveOverflow evmFeeS reserve0 reserve1
            feeTo kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg
            hnumFit (Nat.le_of_not_lt hrootFiveFit),
          uniswapMintFeeRuntimePositiveRootTimesFiveOverflowRevertsOfTail (hov := hov) rd7899 htotalEq hroot
            hrootKNonneg hrootKSize hrootKLastNonneg hnumFit
            (Nat.le_of_not_lt hrootFiveFit) hmem hread64⟩
  · exact Or.inr
      ⟨uniswapMintFeeAfterRoots_positiveNumeratorOverflow evmFeeS reserve0 reserve1 feeTo
          kLast rootK rootKLast hroot hrootKNonneg hrootKSize hrootKLastNonneg
          (Nat.le_of_not_lt hnumFit),
        uniswapMintFeeRuntimePositiveNumeratorOverflowRevertsOfTail (hov := hov) rd7899 htotalEq hroot
          hrootKNonneg hrootKSize hrootKLastNonneg (Nat.le_of_not_lt hnumFit) hmem hread64⟩

end UniswapV2Pair
