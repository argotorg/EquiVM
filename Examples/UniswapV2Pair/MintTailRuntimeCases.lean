import Examples.UniswapV2Pair.MintAfterUpdateCases
import Examples.UniswapV2Pair.UpdateCallRuntimeCases
import Examples.UniswapV2Pair.MintTailMintCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
set_option maxHeartbeats 1000000 in
theorem uniswapMintTailRuntimeCases
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256} {locals : Store} (evm : EVM.State) (recipient : AccountAddress) (fee : Bool)
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
        mintAfterLiquidityTailStmts .reverted ∧
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)) ∨
    (∃ frame' evm' σ',
      ExecBlock config { contract := contract, locals := locals } evm
        mintAfterLiquidityTailStmts (.returned frame' evm'
          (some [uniswapUint256Value liquidity])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = evm.createdAccounts ∧
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee, σ') (UInt256.toByteArray liquidity)) := by
  rcases uniswapMintTailMintCases evm recipient rd3841 hAccounts henv hrecipient hto hliq
      hperm hmem hmem64 with hrev | ⟨_, _, hprefix, hMintAccounts, rd3914, hmemM, hmemM64⟩
  · exact Or.inl hrev
  have henvM : (mintFunctionPostState evm recipient liquidity).executionEnv = I := by
    simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
      storageStore_executionEnv, henv]
  obtain ⟨_, _, rd6959⟩ := uniswapMintRuntimeUpdateEntry rd3914
  have hupdate := uniswapUpdateCallRuntimeCases
    (locals := locals.insert "_mintResult" Value.unit)
    (mintFunctionPostState evm recipient liquidity) rd6959 hMintAccounts henvM
    (by rw [store_get_ne _ _ (by decide), hbalance0])
    (by rw [store_get_ne _ _ (by decide), hbalance1])
    (by rw [store_get_ne _ _ (by decide), hreserve0])
    (by rw [store_get_ne _ _ (by decide), hreserve1])
    hclean0 hclean1 hperm hmemM hmemM64 (by jump_dest) (by simp only [List.length_cons, List.length_nil]; omega)
  rcases hupdate with ⟨hupdate, rdRev⟩ |
    ⟨evmUpd, σUpd, packed, _, _, hupdate, hUpdAccounts, henvUpd, hcreatedUpd,
      rd3926, hmemUpd, hmemUpd64⟩
  · refine Or.inl ⟨?_, rdRev⟩
    simpa only [mintAfterLiquidityTailStmts, updateReservesStmtsWith, List.append_assoc,
      List.cons_append, List.nil_append] using
      execBlock_append hprefix (ExecBlock.consRevert (stmts :=
        [.ite (.var "feeOn")
          [.assign .storage kLastRef
            (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref)))] []] ++
          lockExit ++ [.return [.var "liquidity"]]) hupdate)
  · obtain ⟨evmRet, σRet, hreturn, hRetAccounts, hcreatedRet, rdRet⟩ :=
      uniswapMintAfterUpdateRuntimeReturns
        (locals := (locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit)
        evmUpd fee rd3926 hUpdAccounts henvUpd hflag
        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hfee])
        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hliq])
        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hreserve0Base])
        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hreserve1Base])
        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hkLast])
        (by rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hunlocked])
        hmemUpd hmemUpd64 hperm
    refine Or.inr ⟨⟨contract,
        (locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit⟩,
      evmRet, σRet, ?_, hRetAccounts, ?_, rdRet⟩
    · simpa only [mintAfterLiquidityTailStmts, updateReservesStmtsWith, List.append_assoc,
        List.cons_append, List.nil_append] using
        execBlock_append hprefix (ExecBlock.consNormal hupdate hreturn)
    · rw [hcreatedRet, hcreatedUpd]
      simp only [mintFunctionPostState, mintFunctionAfterTotalSupplyState,
        storageStore_createdAccounts]

end UniswapV2Pair
