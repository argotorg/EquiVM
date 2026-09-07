import Examples.UniswapV2Pair.MintTailMintCases
import Examples.UniswapV2Pair.MintInitialProductOverflow

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialBranchRuntimeCases
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    {locals : Store} (evm : EVM.State)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hAccounts : accountMapEquiv σFee evm.accountMap)
    (henv : evm.executionEnv = I)
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256)))
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (ExecStmt config { contract := contract, locals := locals } evm
        mintLiquidityBranchStmt .reverted ∧
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) ∨
    (∃ root liquidity k' C',
      ExecStmt config { contract := contract, locals := locals } evm
        mintLiquidityBranchStmt
        (.ok ⟨contract, ((locals.insert "rootLiquidity" (.int root)).insert
          "liquidity" (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit⟩
          (mintFunctionPostState evm (AccountAddress.ofNat 0) ⟨1000⟩)) ∧
      accountMapEquiv (mintRuntimeMintMap σFee I ⟨0⟩ ⟨1000⟩ mem)
        (mintFunctionPostState evm (AccountAddress.ofNat 0) ⟨1000⟩).accountMap ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3841⟩
        [⟨0⟩, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
          liquidity, toWord, ⟨861⟩, sel]
        (mintRuntimeMintMem ⟨0⟩ ⟨1000⟩ mem) feeToStaticcallActiveWords rdata
        (cAFee, mintRuntimeMintMap σFee I ⟨0⟩ ⟨1000⟩ mem) k' C' ∧
      (mintRuntimeMintMem ⟨0⟩ ⟨1000⟩ mem).size = 164 ∧
      (mintRuntimeMintMem ⟨0⟩ ⟨1000⟩ mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩) := by
  by_cases hfit : mintAmountProductNat amount0 amount1 < UInt256.size
  · obtain ⟨root, _, _, hsqrt, hrootNonneg, hrootSize, rd2531⟩ :=
      mintInitialLiquiditySqrtPrefixRuntimeBounded ⟨contract, locals⟩ evm rfl
        (evalExprs_mint_initialSqrtArg_of_get evm amount0 amount1 hamount0 hamount1 hfit)
        rd3701 htotalZero hfit
    by_cases hge : minimumLiquidity ≤ root
    · let liquidity := UInt256.ofNat (root - minimumLiquidity).toNat
      have hfitSub : root - minimumLiquidity < (2 : Int) ^ 256 := by
        have hrootLt : root < (UInt256.size : Int) := by
          have h := Int.ofNat_lt.mpr hrootSize
          simpa only [Int.toNat_of_nonneg hrootNonneg] using h
        norm_num [minimumLiquidity, UInt256.size] at hrootLt ⊢
        omega
      obtain ⟨hgeWord, hliquidity⟩ := mintInitialRootLiquidityRuntimeFacts hrootSize hge
        (show liquidity = UInt256.ofNat (root - minimumLiquidity).toNat from rfl)
      have htotalFit :
          (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size := by
        rw [htotalZero]
        native_decide
      have hfitSupply : mintFunctionTotalSupplyNewNat evm ⟨1000⟩ < UInt256.size := by
        rw [mintFunctionTotalSupplyNewNat_eq_runtime hAccounts henv]
        exact htotalFit
      have hbalanceEq := mintFunctionToBalanceNewNat_eq_runtimeMintRecipient
        (recipientWord := (⟨0⟩ : UInt256)) (recipient := AccountAddress.ofNat 0) (mem := mem) hAccounts henv rfl
        (by rw [hmem]; omega) hfitSupply
      by_cases hfitBalance :
          mintFunctionToBalanceNewNat evm (AccountAddress.ofNat 0) ⟨1000⟩ < UInt256.size
      · have hbalanceFit := hfitBalance
        rw [hbalanceEq] at hbalanceFit
        obtain ⟨_, _, rd3841⟩ := uniswapMintRuntimeInitialLiquidityAfterRootEntry rd2531
          hliquidity hgeWord hperm htotalFit hbalanceFit hmem hmem64
        refine Or.inr ⟨root, liquidity, _, _,
          uniswapMintInitialLiquidityBranchStmtPrefix evm root liquidity htotal hsqrt hge
            hfitSub rfl hfitSupply hfitBalance,
          accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient
            hAccounts henv rfl (by rw [hmem]; omega) hfitSupply hfitBalance,
          rd3841, ?_, ?_⟩
        · exact (uniswapInternalMintSuccessMem_size_of_ge160 ⟨0⟩ ⟨1000⟩
            (by rw [hmem]; omega)).trans hmem
        · exact uniswapInternalMintSuccessMem_read64_of_ge160 ⟨0⟩ ⟨1000⟩
            (by rw [hmem]; omega) hmem64
      · obtain ⟨_, _, rd8128⟩ := uniswapMintRuntimeInitialMinimumMintEntry rd2531
          hliquidity hgeWord
        exact Or.inl ⟨uniswapMintInitialLiquidityBranchStmtMinimumMintBalanceOverflowReverts
          evm root liquidity htotal hsqrt hge hfitSub rfl hfitSupply
            (Nat.le_of_not_lt hfitBalance),
          uniswapInternalMintRuntimeBalanceOverflowReverts rd8128 hperm htotalFit
            (by rw [← hbalanceEq]; exact Nat.le_of_not_lt hfitBalance) hmem hmem64
            (by simp only [List.length_cons, List.length_nil]; omega)⟩
    · have hlt : root < minimumLiquidity := lt_of_not_ge hge
      refine Or.inl ⟨uniswapMintInitialLiquidityBranchStmtUnderflowReverts evm root htotal
        hsqrt hlt, uniswapMintRuntimeInitialLiquidityAfterRootUnderflowReverts rd2531
          ?_ hmem hmem64⟩
      rw [ulit_toNat' _ hrootSize]
      have h : root.toNat < 1000 := by
        have hc := Int.toNat_of_nonneg hrootNonneg
        norm_num [minimumLiquidity] at hlt
        omega
      exact h
  · obtain ⟨_, _, rd3713⟩ := uniswapMintRuntimeAfterMintFeeTotalSupplyZero rd3701 htotalZero
    exact Or.inl ⟨uniswapMintInitialLiquidityBranchStmtProductOverflowReverts evm
      amount0 amount1 htotal hamount0 hamount1 (Nat.le_of_not_lt hfit),
      uniswapMintRuntimeInitialLiquidityProductOverflowReverts rd3713
        (Nat.le_of_not_lt hfit) hmem hmem64⟩

end UniswapV2Pair
