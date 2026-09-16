import Examples.UniswapV2Pair.BurnAmountsSource

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach
namespace UniswapV2Pair
set_option maxRecDepth 2000000

set_option maxHeartbeats 1000000 in
theorem uniswapBurnAmountsRuntimeCases
    {g : Sat256} {s0 : State} {I : ExecutionEnv}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {mem rdata : ByteArray} {feeOn totalSupply liquidity balance0 balance1
      token0 token1 reserve0 reserve1 : UInt256} {R : List UInt256} {k C : ℕ}
    {locals : Store} (evm : EVM.State)
    (rd4479 : RD uniswapV2PairBytecode I g s0 ⟨4479⟩
      (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
        reserve1 :: reserve0 :: ⟨0⟩ :: ⟨0⟩ :: R)
      mem feeToStaticcallActiveWords rdata acc k C)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hb0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hb1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (hmem : mem.size = 164)
    (hread64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 32 ≤ 1024) :
    (ExecBlock config { contract := contract, locals := locals } evm
        [burnAmount0Stmt, burnAmount1Stmt] .reverted ∧
      (RDrev uniswapV2PairBytecode g s0 ∨ RDinvalid uniswapV2PairBytecode g s0)) ∨
    (∃ k' C',
      ExecBlock config { contract := contract, locals := locals } evm
        [burnAmount0Stmt, burnAmount1Stmt]
        (.ok { contract := contract, locals := burnAmountsStore locals liquidity balance0 balance1 totalSupply } evm) ∧
      RD uniswapV2PairBytecode I g s0 ⟨4533⟩
        (totalSupply :: feeOn :: liquidity :: balance1 :: balance0 :: token1 :: token0 ::
          reserve1 :: reserve0 :: burnAmountWord liquidity balance1 totalSupply ::
          burnAmountWord liquidity balance0 totalSupply :: R)
        mem feeToStaticcallActiveWords rdata acc k' C') := by
  obtain ⟨_, _, rdMul0⟩ := uniswapBurnRuntimeAmount0MulEntry rd4479
    (by simp only [List.length_cons]; omega)
  by_cases hfit0 : mintAmountProductNat liquidity balance0 < UInt256.size
  · obtain ⟨_, _, rd4495⟩ := RD.uniswapSafeMathMulSuccess rdMul0 hfit0
      (by jump_dest) (by simp only [List.length_cons]; omega)
    by_cases hz : totalSupply = ⟨0⟩
    · have hsource : ExecBlock config { contract := contract, locals := locals } evm
          [burnAmount0Stmt, burnAmount1Stmt] .reverted :=
        ExecBlock.consRevert (ExecStmt.letDeclRevert
          (evalExpr_burn_amount_divZero evm "balance0" liquidity balance0 hliq hb0
            (by simpa only [hz] using htotal) hfit0))
      rw [hz] at rd4495
      exact Or.inl ⟨hsource, Or.inr (uniswapBurnRuntimeAmount0DivZero rd4495
        (by simp only [List.length_cons]; omega))⟩
    · obtain ⟨_, _, rd4506⟩ := uniswapBurnRuntimeAmount0Computed rd4495 hz (by omega)
      obtain ⟨_, _, rdMul1⟩ := uniswapBurnRuntimeAmount1MulEntry rd4506
        (by simp only [List.length_cons]; omega)
      by_cases hfit1 : mintAmountProductNat liquidity balance1 < UInt256.size
      · obtain ⟨_, _, rd4522⟩ := RD.uniswapSafeMathMulSuccess rdMul1 hfit1
          (by jump_dest) (by simp only [List.length_cons]; omega)
        obtain ⟨k', C', rd4533⟩ := uniswapBurnRuntimeAmount1Computed rd4522 hz (by omega)
        refine Or.inr ⟨k', C', uniswapBurnAmountsSourceSuccess evm liquidity balance0 balance1
          totalSupply hliq hb0 hb1 htotal hfit0 hfit1 hz, ?_⟩
        simpa only [burnAmountWord, mintProportionalLiquidityWord,
          mintAmountProductWord_eq_mul _ _ hfit0, mintAmountProductWord_eq_mul _ _ hfit1]
          using rd4533
      · exact Or.inl ⟨uniswapBurnAmountsSourceRevert_product1 evm liquidity balance0 balance1
          totalSupply hliq hb0 hb1 htotal hfit0 (Nat.le_of_not_lt hfit1) hz,
          Or.inl (RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164 rdMul1
            (Nat.le_of_not_lt hfit1) hmem hread64
            (by simp only [List.length_cons]; omega))⟩
  · exact Or.inl ⟨ExecBlock.consRevert (ExecStmt.letDeclRevert
        (evalExpr_burn_amount_productOverflow evm "balance0" liquidity balance0 hliq hb0
          (Nat.le_of_not_lt hfit0))),
      Or.inl (RD.uniswapSafeMathMulOverflow_feeToStaticcall_size164 rdMul0
        (Nat.le_of_not_lt hfit0) hmem hread64 (by simp only [List.length_cons]; omega))⟩

end UniswapV2Pair
