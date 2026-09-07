import Examples.UniswapV2Pair.MintInitialBranchRuntimeCases
import Examples.UniswapV2Pair.MintTailRuntimeCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialRuntimeCases
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256} {locals : Store} (evm : EVM.State) (recipient : AccountAddress) (fee : Bool)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0,
        ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hAccounts : accountMapEquiv σFee evm.accountMap)
    (henv : evm.executionEnv = I)
    (hrecipient : recipient = AccountAddress.ofNat toWord.toNat)
    (hto : locals.get? "to" = some (.address recipient))
    (htotalZero : uniswapSlotWord ⟨0⟩ σFee I = ⟨0⟩)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256)))
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hflag : feeOn = if fee then ⟨1⟩ else ⟨0⟩)
    (hfee : locals.get? "feeOn" = some (.bool fee))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hkLast : locals.get? "kLast" = none)
    (hunlocked : locals.get? "unlocked" = none)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hperm : I.perm = true)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    (ExecBlock config { contract := contract, locals := locals } evm
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts) .reverted ∧
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) ∨
    (∃ liquidity frame' evm' σ',
      ExecBlock config { contract := contract, locals := locals } evm
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts) (.returned frame' evm'
          (some [uniswapUint256Value liquidity])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = evm.createdAccounts ∧
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee, σ') (UInt256.toByteArray liquidity)) := by
  rcases uniswapMintInitialBranchRuntimeCases evm rd3701 hAccounts henv htotalZero htotal
      hamount0 hamount1 hperm hmem hmem64 with ⟨hrev, rdRev⟩ |
      ⟨root, liquidity, _, _, hbranch, hMinAccounts, rd3841, hmemMin, hmemMin64⟩
  · exact Or.inl ⟨ExecBlock.consRevert hrev, rdRev⟩
  have henvMin : (mintFunctionPostState evm (AccountAddress.ofNat 0) ⟨1000⟩).executionEnv = I := by
    simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
      storageStore_executionEnv, henv]
  have htail := uniswapMintTailRuntimeCases
    (locals := ((locals.insert "rootLiquidity" (.int root)).insert
      "liquidity" (uniswapUint256Value liquidity)).insert "_minimumMint" Value.unit)
    (mintFunctionPostState evm (AccountAddress.ofNat 0) ⟨1000⟩) recipient fee rd3841
    hMinAccounts henvMin hrecipient
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hto])
    (by rw [store_get_ne _ _ (by decide), store_get_self]) hflag
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hfee])
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance0])
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance1])
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0])
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1])
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0Base])
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1Base])
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hkLast])
    (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hunlocked])
    hclean0 hclean1 hperm hmemMin hmemMin64
  rcases htail with ⟨hrev, rdRev⟩ | ⟨frameRet, evmRet, σRet, hreturn, hRetAccounts,
    hcreatedRet, rdRet⟩
  · exact Or.inl ⟨ExecBlock.consNormal hbranch hrev, rdRev⟩
  · refine Or.inr ⟨liquidity, frameRet, evmRet, σRet, ExecBlock.consNormal hbranch hreturn,
      hRetAccounts, ?_, rdRet⟩
    rw [hcreatedRet]
    simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
      storageStore_createdAccounts]

end UniswapV2Pair

