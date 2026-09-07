import Examples.UniswapV2Pair.MintInitialSecondMintReverts
import Examples.UniswapV2Pair.MintRuntimeFitBridge
import Examples.UniswapV2Pair.MintLiquidityZeroRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

noncomputable abbrev mintRuntimeMintMap (σ : AccountMap) (I : ExecutionEnv)
    (recipient value : UInt256) (mem : ByteArray) : AccountMap :=
  sstoreAccountMap I.codeOwner
    (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + value))
    (uniswapInternalMintBalanceHashSlot recipient
      (uniswapInternalMintBalanceHashMem recipient mem))
    (uniswapCodeOwnerStorageWord I
      (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + value))
      (uniswapInternalMintBalanceHashSlot recipient mem) + value)

noncomputable abbrev mintRuntimeMintMem (recipient value : UInt256) (mem : ByteArray) : ByteArray :=
  uniswapInternalMintLogMem value
    (uniswapInternalMintBalanceHashMem recipient
      (uniswapInternalMintBalanceHashMem recipient mem))

set_option maxRecDepth 2000000 in
theorem uniswapMintTailMintCases
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (rd3841 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3841⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hAccounts : accountMapEquiv σFee evm.accountMap)
    (henv : evm.executionEnv = I)
    (hrecipient : recipient = AccountAddress.ofNat toWord.toNat)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (ExecBlock config { contract := contract, locals := locals } evm
        mintAfterLiquidityTailStmts .reverted ∧
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) ∨
    (∃ k' C',
      ExecBlock config { contract := contract, locals := locals } evm
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ]
        (.ok (resumeAfterInternalCall { contract := contract, locals := locals }
          "_mintResult" none) (mintFunctionPostState evm recipient liquidity)) ∧
      accountMapEquiv (mintRuntimeMintMap σFee I toWord liquidity mem)
        (mintFunctionPostState evm recipient liquidity).accountMap ∧
      RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3914⟩
        [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
          liquidity, toWord, ⟨861⟩, sel]
        (mintRuntimeMintMem toWord liquidity mem) feeToStaticcallActiveWords rdata
        (cAFee, mintRuntimeMintMap σFee I toWord liquidity mem) k' C' ∧
      (mintRuntimeMintMem toWord liquidity mem).size = 164 ∧
      (mintRuntimeMintMem toWord liquidity mem).readWithPadding 64 32 =
        UInt256.toByteArray ⟨128⟩) := by
  by_cases hz : liquidity = ⟨0⟩
  · exact Or.inl ⟨uniswapMintAfterLiquidityZeroReverts evm (by simpa only [hz] using hliq),
      uniswapMintRuntimeLiquidityZeroReverts rd3841 hz hmem hmem64⟩
  obtain ⟨_, _, rd8128⟩ := uniswapMintRuntimeLiquidityMintEntry rd3841 hz
  have htotalEq := mintFunctionTotalSupplyNewNat_eq_runtime
    (liquidity := liquidity) hAccounts henv
  by_cases hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size
  · have htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size := by
      rwa [← htotalEq]
    have hbalanceEq := mintFunctionToBalanceNewNat_eq_runtimeMintRecipient
      (mem := mem) hAccounts henv hrecipient (by rw [hmem]; omega) hfitSupply
    by_cases hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size
    · have hbalanceFit := hfitBalance
      rw [hbalanceEq] at hbalanceFit
      obtain ⟨_, _, rd3914⟩ := uniswapInternalMintRuntimeSuccess rd8128 hperm
        htotalFit hbalanceFit
        (uniswapInternalMintDoubleBalanceHashMem_mload64_of_ge160 toWord
          (by rw [hmem]; omega) hmem64)
        (uniswapInternalMintSuccessMem_mload64_of_ge160 toWord liquidity
          (by rw [hmem]; omega) hmem64)
        (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
      exact Or.inr ⟨_, _,
        uniswapMintLiquidityMintPrefix evm recipient liquidity hto hliq hz
          hfitSupply hfitBalance,
        accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient
          hAccounts henv hrecipient (by rw [hmem]; omega) hfitSupply hfitBalance,
        rd3914,
        (uniswapInternalMintSuccessMem_size_of_ge160 toWord liquidity
          (by rw [hmem]; omega)).trans hmem,
        uniswapInternalMintSuccessMem_read64_of_ge160 toWord liquidity
          (by rw [hmem]; omega) hmem64⟩
    · exact Or.inl ⟨uniswapMintAfterLiquidityMintBalanceOverflowReverts evm recipient
        liquidity hto hliq hz hfitSupply (Nat.le_of_not_lt hfitBalance),
        uniswapInternalMintRuntimeBalanceOverflowReverts rd8128 hperm htotalFit
          (by rw [← hbalanceEq]; exact Nat.le_of_not_lt hfitBalance) hmem hmem64
          (by simp only [List.length_cons, List.length_nil]; omega)⟩
  · exact Or.inl ⟨uniswapMintAfterLiquidityMintTotalSupplyOverflowReverts evm recipient
      liquidity hto hliq hz (Nat.le_of_not_lt hfitSupply),
      uniswapInternalMintRuntimeTotalSupplyOverflowReverts rd8128
        (by rw [← htotalEq]; exact Nat.le_of_not_lt hfitSupply) hmem hmem64
        (by simp only [List.length_cons, List.length_nil]; omega)⟩

end UniswapV2Pair
