import Examples.UniswapV2Pair.MintProportionalProductOverflow
import Examples.UniswapV2Pair.MintProportionalDivZero

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
theorem uniswapMintProportionalArithmeticCases
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    {locals : Store} (evm : EVM.State)
    (rd3762 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3762⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat))) :
    (mintAmountProductNat amount0 totalSupply < UInt256.size ∧
      reserve0 ≠ ⟨0⟩ ∧ mintAmountProductNat amount1 totalSupply < UInt256.size ∧
      reserve1 ≠ ⟨0⟩) ∨
    (ExecStmt config { contract := contract, locals := locals } evm
      mintLiquidityBranchStmt .reverted ∧
      (RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ∨
        RDinvalid uniswapV2PairBytecode (Sat256.ofUInt256 g)
          (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I))) := by
  by_cases hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size
  · by_cases hz0 : reserve0 = ⟨0⟩
    · have hsource := uniswapMintProportionalLiquidity0DivZeroReverts evm amount0
        totalSupply htotal htotalNonzero hamount0 (by simpa only [hz0] using hreserve0) hfit0
      obtain ⟨_, _, rdMul⟩ := RD.uniswapMintProportionalMul0Entry rd3762 hclean0
        (by simp only [List.length_cons, List.length_nil]; omega)
      obtain ⟨_, _, rdDiv⟩ := RD.uniswapSafeMathMulSuccess
        (a := amount0) (b := totalSupply) rdMul hfit0 (by jump_dest)
        (by simp only [List.length_cons, List.length_nil]; omega)
      rw [hz0] at rdDiv
      exact Or.inr ⟨hsource, Or.inr (RD.uniswapMintProportionalDiv0Zero rdDiv
        (by simp only [List.length_cons, List.length_nil]; omega))⟩
    · by_cases hfit1 : mintAmountProductNat amount1 totalSupply < UInt256.size
      · by_cases hz1 : reserve1 = ⟨0⟩
        · have hsource := uniswapMintProportionalLiquidity1DivZeroReverts evm amount0
            amount1 totalSupply reserve0 htotal htotalNonzero hamount0 hamount1 hreserve0
            (by simpa only [hz1] using hreserve1) hfit0 hfit1 hz0
          obtain ⟨_, _, rd3800⟩ := uniswapMintRuntimeProportionalLiquidity0Entry rd3762
            hclean0 hfit0 hz0
          obtain ⟨_, _, rdMul⟩ := RD.uniswapMintProportionalMul1Entry rd3800 hclean1
            (by simp only [List.length_cons, List.length_nil]; omega)
          obtain ⟨_, _, rdDiv⟩ := RD.uniswapSafeMathMulSuccess
            (a := amount1) (b := totalSupply) rdMul hfit1 (by jump_dest)
            (by simp only [List.length_cons, List.length_nil]; omega)
          rw [hz1] at rdDiv
          exact Or.inr ⟨hsource, Or.inr (RD.uniswapMintProportionalDiv1Zero rdDiv
            (by simp only [List.length_cons, List.length_nil]; omega))⟩
        · exact Or.inl ⟨hfit0, hz0, hfit1, hz1⟩
      · have hover : UInt256.size ≤ amount1.toNat * totalSupply.toNat := Nat.le_of_not_lt hfit1
        exact Or.inr ⟨uniswapMintProportionalLiquidity1ProductOverflowReverts evm
          amount0 amount1 totalSupply reserve0 htotal htotalNonzero hamount0 hamount1
          hreserve0 hfit0 hz0 hover,
          Or.inl (uniswapMintRuntimeProportionalLiquidity1ProductOverflowReverts rd3762
            hclean0 hclean1 hfit0 hz0 hover hmem hmem64)⟩
  · have hover : UInt256.size ≤ amount0.toNat * totalSupply.toNat := Nat.le_of_not_lt hfit0
    exact Or.inr ⟨uniswapMintProportionalLiquidity0ProductOverflowReverts evm amount0
      totalSupply htotal htotalNonzero hamount0 hover,
      Or.inl (uniswapMintRuntimeProportionalLiquidity0ProductOverflowReverts rd3762
        hclean0 hover hmem hmem64)⟩

end UniswapV2Pair
