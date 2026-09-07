import Examples.UniswapV2Pair.MintFeeRootArithmeticCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

-- Split on the actual roots produced by the shared sqrt routine.
theorem uniswapMintFeeActualRootArithmeticCases
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State} {mem rdata : ByteArray} {k C : ℕ}
    {rootK rootKLast : Int} {feeTo : AccountAddress}
    {kLast feeToWord amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (rd7899 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨7899⟩
      [UInt256.ofNat rootKLast.toNat, ⟨0⟩, UInt256.ofNat rootK.toNat, kLast, feeToWord,
        ⟨1⟩, reserve1, reserve0, ⟨3701⟩, ⟨0⟩, amount1, amount0, balance1,
        balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = uniswapSlotWord ⟨0⟩ σFee I)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hrootKLastSize : rootKLast.toNat < UInt256.size)
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size ∧
      mintFeeRootTimesFiveNat rootK < UInt256.size ∧
      mintFeeDenominatorNat rootK rootKLast < UInt256.size) ∨
    (ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast)
      evmFeeS [mintFeeRootComparisonStmt] .reverted ∧
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) := by
  exact uniswapMintFeeActualRootArithmeticCasesOfTail rd7899 htotalEq hroot hrootKNonneg
    hrootKSize hrootKLastNonneg hrootKLastSize hmem hread64
    (by simp only [List.length_cons, List.length_nil]; omega)

end UniswapV2Pair
