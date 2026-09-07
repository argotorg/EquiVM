import Examples.UniswapV2Pair.MintProportionalRuntimeCalls
import Examples.UniswapV2Pair.MintSourceReturns

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem evalExpr_mint_proportionalLiquidity_divZero
    {locals : Store} (evm : EVM.State) (amountName reserveName : Ident)
    (amount totalSupply : UInt256)
    (hamount : locals.get? amountName = some (uniswapUint256Value amount))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hreserve : locals.get? reserveName = some (.int 0))
    (hfit : mintAmountProductNat amount totalSupply < UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (.binary .div
        (u256 (.binary .mul (.var amountName) (.var "_totalSupply")))
        (.var reserveName)) = .revert := by
  have hmul := evalExpr_mint_namedProduct_of_get evm amountName "_totalSupply"
    amount totalSupply hamount htotal hfit
  simp only [evalExpr?, hmul, EvalResult.ofOption, hreserve, EvalResult.bind, bind,
    mintAmountProductValue, uniswapUint256Value, uint256Value, evalBinaryOp?, ite_true]

theorem uniswapMintProportionalLiquidity0DivZeroReverts
    {locals : Store} (evm : EVM.State) (amount0 totalSupply : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hreserve0 : locals.get? "_reserve0" = some (.int 0))
    (hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size) :
    ExecStmt config { contract := contract, locals := locals } evm
      mintLiquidityBranchStmt .reverted := by
  refine ExecStmt.iteFalse
    (evalExpr_mint_totalSupply_eq_zero_false evm totalSupply htotal htotalNonzero) ?_
  exact ExecBlock.consRevert (ExecStmt.letDeclRevert
    (evalExpr_mint_proportionalLiquidity_divZero evm "amount0" "_reserve0" amount0
      totalSupply hamount0 htotal hreserve0 hfit0))

theorem uniswapMintProportionalLiquidity1DivZeroReverts
    {locals : Store} (evm : EVM.State) (amount0 amount1 totalSupply reserve0 : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int 0))
    (hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 totalSupply < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩) :
    ExecStmt config { contract := contract, locals := locals } evm
      mintLiquidityBranchStmt .reverted := by
  have hliq0 := evalExpr_mint_proportionalLiquidity_of_get evm "amount0" "_reserve0"
    amount0 totalSupply reserve0 hamount0 htotal hreserve0 hfit0 hreserve0Nonzero
  have hliq1 := evalExpr_mint_proportionalLiquidity_divZero
    (locals := locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0))
    evm "amount1" "_reserve1" amount1 totalSupply
    (by rw [store_get_ne _ _ (by decide), hamount1])
    (by rw [store_get_ne _ _ (by decide), htotal])
    (by rw [store_get_ne _ _ (by decide), hreserve1]) hfit1
  refine ExecStmt.iteFalse
    (evalExpr_mint_totalSupply_eq_zero_false evm totalSupply htotal htotalNonzero) ?_
  exact ExecBlock.consNormal (ExecStmt.letDecl hliq0)
    (ExecBlock.consRevert (ExecStmt.letDeclRevert hliq1))

set_option maxRecDepth 2000000 in
theorem RD.uniswapMintProportionalDiv0Zero
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {product : UInt256}
    (rd : RD uniswapV2PairBytecode ee g s0 ⟨3791⟩
      (product :: ⟨0⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 4 ≤ 1024) : RDinvalid uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rdGuard⟩ := RD.uniswapMintProportionalDiv0Guard rd hov
  have rdInvalid := evm_run rdGuard with [jumpiNT (by native_decide)]
  exact RD.invalidHalt rdInvalid (by native_decide)

set_option maxRecDepth 2000000 in
theorem RD.uniswapMintProportionalDiv1Zero
    {g : Sat256} {s0 : State} {ee : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {aw : UInt256} {k C : ℕ} {R : List UInt256}
    {product : UInt256}
    (rd : RD uniswapV2PairBytecode ee g s0 ⟨3825⟩
      (product :: ⟨0⟩ :: R) mem aw rdata acc k C)
    (hov : R.length + 4 ≤ 1024) : RDinvalid uniswapV2PairBytecode g s0 := by
  obtain ⟨_, _, rdGuard⟩ := RD.uniswapMintProportionalDiv1Guard rd hov
  have rdInvalid := evm_run rdGuard with [jumpiNT (by native_decide)]
  exact RD.invalidHalt rdInvalid (by native_decide)

end UniswapV2Pair
