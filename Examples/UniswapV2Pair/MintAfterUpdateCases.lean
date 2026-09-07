import Examples.UniswapV2Pair.MintRuntimeAfterFee
import Examples.UniswapV2Pair.MintSourceReturns
import Examples.UniswapV2Pair.MintReserveProductFits

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

set_option maxRecDepth 2000000 in
theorem uniswapMintAfterUpdateRuntimeReturns
    {cA gh bl σ σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σUpd : AccountMap}
    {mem rdata : ByteArray} {k C : ℕ}
    {totalSupply feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256} {locals : Store} (evm : EVM.State) (fee : Bool)
    (rd3926 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I) ⟨3926⟩
      [totalSupply, feeOn, amount1, amount0, balance1, balance0, reserve1, reserve0,
        liquidity, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σUpd) k C)
    (hAccounts : accountMapEquiv σUpd evm.accountMap)
    (henv : evm.executionEnv = I)
    (hflag : feeOn = if fee then ⟨1⟩ else ⟨0⟩)
    (hfee : locals.get? "feeOn" = some (.bool fee))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hreserve0 : locals.get? "reserve0" = none)
    (hreserve1 : locals.get? "reserve1" = none)
    (hkLast : locals.get? "kLast" = none)
    (hunlocked : locals.get? "unlocked" = none)
    (hmem : mem.size = 192)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hperm : I.perm = true) :
    ∃ evm' σ',
      ExecBlock config { contract := contract, locals := locals } evm
        ([.ite (.var "feeOn")
          [.assign .storage kLastRef
            (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref)))] []] ++
          lockExit ++ [.return [.var "liquidity"]])
        (.returned { contract := contract, locals := locals } evm'
          (some [uniswapUint256Value liquidity])) ∧
      accountMapEquiv σ' evm'.accountMap ∧ evm'.createdAccounts = evm.createdAccounts ∧
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee, σ') (UInt256.toByteArray liquidity) := by
  cases fee with
  | false =>
    refine ⟨uniswapLockExitedState evm, _,
      uniswapMintAfterUpdateFeeOffReturn evm liquidity hfee hliq hunlocked, ?_, ?_,
      uniswapMintRuntimeAfterUpdateFeeOffReturns rd3926 hflag hmem hmem64 hperm⟩
    · simpa only [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap,
        henv] using accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hAccounts
    · simp only [uniswapLockExitedState, uniswapUnlockedState, storageStore_createdAccounts]
  | true =>
    have hslot8 : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σUpd I := by
      have h := accountMapEquiv_storage_findD hAccounts I.codeOwner ⟨8⟩ ⟨0⟩
      simpa only [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
        uniswapSlotWord, henv] using h.symm
    have hkLastValue :
        mintFeeReserveProductWord (uniswapReserve0Word evm) (uniswapReserve1Word evm) =
          UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask)
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
              reserve112Mask) := by
      rw [mintFeeReserveProductWord_eq_mul _ _ (mintFeeReserveProductNat_source_lt evm)]
      simp only [uniswapReserve0Word, uniswapReserve1Word, hslot8]
    have hKLastAccounts := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩
      (mintFeeReserveProductWord (uniswapReserve0Word evm) (uniswapReserve1Word evm)) hAccounts
    have hAfterKLast : accountMapEquiv
        (sstoreAccountMap I.codeOwner σUpd ⟨11⟩
          (UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Mask)
            (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σUpd I) reserve112Shift)
              reserve112Mask))) (mintKLastUpdatedState evm).accountMap := by
      simpa only [mintKLastUpdatedState, storageStore_accountMap, henv, hkLastValue]
        using hKLastAccounts
    refine ⟨uniswapLockExitedState (mintKLastUpdatedState evm), _,
      uniswapMintAfterUpdateFeeOnReturn evm liquidity hfee hliq hreserve0 hreserve1
        hkLast hunlocked (mintFeeReserveProductNat_source_lt evm), ?_, ?_,
      uniswapMintRuntimeAfterUpdateFeeOnReturns rd3926
        (by rw [hflag]; native_decide) (mintFeeReserveProductNat_masked_lt _) hmem hmem64 hperm⟩
    · simpa only [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap,
        storageStore_executionEnv, mintKLastUpdatedState, henv]
        using accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hAfterKLast
    · simp only [uniswapLockExitedState, uniswapUnlockedState, mintKLastUpdatedState,
        storageStore_createdAccounts]

end UniswapV2Pair
