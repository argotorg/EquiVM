import Examples.UniswapV2Pair.MintFeeActualRoots
import Examples.UniswapV2Pair.MintFeeAfterRootsRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem mintFeeDenominatorWord_ne_zero_of_fits
    {rootK rootKLast : Int} (hroot : rootK > rootKLast) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size) :
    (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0 := by
  rw [mintFeeDenominatorWord, ulit_toNat' _ hdenFit]
  unfold mintFeeDenominatorNat
  rw [mintFeeRootTimesFiveWord, ulit_toNat' _ hrootFiveFit]
  have hcast := Int.toNat_of_nonneg (show 0 ≤ rootK by omega)
  have hrootPos : 0 < rootK.toNat := by omega
  unfold mintFeeRootTimesFiveNat
  omega

theorem mintFeeLiquidityInt_toNat_lt (evm : EVM.State) (rootK rootKLast : Int) :
    (mintFeeLiquidityInt evm rootK rootKLast).toNat < UInt256.size := by
  unfold mintFeeLiquidityInt
  change (((mintFeeNumeratorWord evm rootK rootKLast).toNat : Int) /
    ((mintFeeDenominatorWord rootK rootKLast).toNat : Int)).toNat < UInt256.size
  rw [← Int.natCast_ediv, Int.toNat_natCast]
  exact lt_of_le_of_lt (Nat.div_le_self _ _)
    (mintFeeNumeratorWord evm rootK rootKLast).val.isLt

set_option maxRecDepth 2000000 in
theorem uniswapMintFeeAfterRoots_mintCallReverts
    (evm : EVM.State) (reserve0 reserve1 : UInt256) (feeTo : AccountAddress)
    (kLast : UInt256) (rootK rootKLast : Int)
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evm rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : mintFeeLiquidityInt evm rootK rootKLast > 0)
    (hmint : ExecStmt config
      (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      (.internalCall "_mint" [.var "feeTo", .var "liquidity"] "_feeMint") .reverted) :
    ExecBlock config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      [mintFeeRootComparisonStmt] .reverted := by
  have hnumStmt : ExecStmt config
      (mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      (.letDecl "numerator" (some uint256)
        (u256 (.binary .mul (.storage totalSupplyRef)
          (u256 (.binary .sub (.var "rootK") (.var "rootKLast"))))))
      (.ok (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm) := ExecStmt.letDecl
    (evalExpr_mintFee_numerator evm reserve0 reserve1 feeTo true kLast rootK rootKLast
      hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit)
  have hdenStmt : ExecStmt config
      (mintFeeAfterNumeratorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      (.letDecl "denominator" (some uint256)
        (u256 (.binary .add (u256 (.binary .mul (.var "rootK") (.intLit 5)))
          (.var "rootKLast"))))
      (.ok (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm) := ExecStmt.letDecl
    (evalExpr_mintFee_denominator evm reserve0 reserve1 feeTo true kLast rootK rootKLast
      hrootKNonneg hrootKLastNonneg hrootFiveFit hdenFit)
  have hliqStmt : ExecStmt config
      (mintFeeAfterDenominatorFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast) evm
      (.letDecl "liquidity" (some uint256)
        (.binary .div (.var "numerator") (.var "denominator")))
      (.ok (mintFeeAfterLiquidityFrame evm reserve0 reserve1 feeTo true kLast rootK rootKLast)
        evm) := ExecStmt.letDecl
    (evalExpr_mintFee_liquidity evm reserve0 reserve1 feeTo true kLast rootK rootKLast hdenom)
  exact ExecBlock.consRevert (ExecStmt.iteTrue
    (evalExpr_mintFee_rootK_gt_rootKLast_true evm reserve0 reserve1 feeTo true kLast
      rootK rootKLast hroot)
    (ExecBlock.consNormal hnumStmt (ExecBlock.consNormal hdenStmt
      (ExecBlock.consNormal hliqStmt (ExecBlock.consRevert (ExecStmt.iteTrue
        (evalExpr_mintFee_liquidity_gt_zero_true evm reserve0 reserve1 feeTo true kLast
          rootK rootKLast hliq) (ExecBlock.consRevert hmint)))))))

end UniswapV2Pair
