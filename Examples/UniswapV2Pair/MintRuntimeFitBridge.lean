import Examples.UniswapV2Pair.MintInternalMintRuntime

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem mintFunctionTotalSupplyNewNat_eq_runtime
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv} {liquidity : UInt256}
    (hPost : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I) :
    mintFunctionTotalSupplyNewNat evm liquidity =
      (uniswapSlotWord ⟨0⟩ σ I).toNat + liquidity.toNat := by
  have htotalEq : mintFunctionTotalSupplyWord evm = uniswapSlotWord ⟨0⟩ σ I :=
    mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPost henv
  simp [mintFunctionTotalSupplyNewNat, htotalEq]

theorem mintFunctionToBalanceNewNat_eq_runtimeMintRecipient
    {σ : AccountMap} {evm : EVM.State} {I : ExecutionEnv} {mem : ByteArray}
    {liquidity recipientWord : UInt256} {recipient : AccountAddress}
    (hPost : accountMapEquiv σ evm.accountMap)
    (henv : evm.executionEnv = I)
    (hrecipient : recipient = AccountAddress.ofNat recipientWord.toNat)
    (hmem : 64 ≤ mem.size)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size) :
    mintFunctionToBalanceNewNat evm recipient liquidity =
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
        (uniswapInternalMintBalanceHashSlot recipientWord mem)).toNat + liquidity.toNat := by
  have htotalEq : mintFunctionTotalSupplyWord evm = uniswapSlotWord ⟨0⟩ σ I :=
    mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPost henv
  have hnewSupply :
      mintFunctionTotalSupplyNewWord evm liquidity =
        uniswapSlotWord ⟨0⟩ σ I + liquidity := by
    simpa [mintFunctionTotalSupplyNewWord, mintFunctionTotalSupplyNewNat, htotalEq]
      using u256_ofNat_toNat_add_eq_add_of_lt (uniswapSlotWord ⟨0⟩ σ I) liquidity
        (by simpa [mintFunctionTotalSupplyNewNat, htotalEq] using hfitSupply)
  have hafterTotal :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
        (mintFunctionAfterTotalSupplyState evm liquidity).accountMap := by
    have hstore := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨0⟩
      (uniswapSlotWord ⟨0⟩ σ I + liquidity) hPost
    simpa [mintFunctionAfterTotalSupplyState, henv, storageStore_accountMap, hnewSupply]
      using hstore
  have henvAfter : (mintFunctionAfterTotalSupplyState evm liquidity).executionEnv = I := by
    simp [mintFunctionAfterTotalSupplyState, henv, storageStore_executionEnv]
  have hslotSource :
      mintFunctionToSlot recipient = mapSlot (UInt256.land recipientWord solcAddrMask) ⟨1⟩ := by
    subst recipient
    unfold mintFunctionToSlot balanceOfSlot mintFunctionToKey
    rw [keyValueToWord_address_ofNat_mask]
    rw [u256_land_comm solcAddrMask recipientWord]
  have hslotRuntime :
      uniswapInternalMintBalanceHashSlot recipientWord mem =
        mapSlot (UInt256.land recipientWord solcAddrMask) ⟨1⟩ := by
    exact uniswapInternalMintBalanceHashSlot_eq_mapSlot recipientWord hmem
  have hbalanceEq :
      mintFunctionToBalanceWord evm recipient liquidity =
        uniswapCodeOwnerStorageWord I
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (uniswapSlotWord ⟨0⟩ σ I + liquidity))
          (uniswapInternalMintBalanceHashSlot recipientWord mem) := by
    have hword := accountMapEquiv_storage_findD hafterTotal I.codeOwner
      (mapSlot (UInt256.land recipientWord solcAddrMask) ⟨1⟩) ⟨0⟩
    simpa [mintFunctionToBalanceWord, uniswapCodeOwnerStorageWord, Solm.EVM.storageLoad,
      State.lookupAccount, Account.lookupStorage, henv, henvAfter, hslotSource, hslotRuntime]
      using hword.symm
  simp [mintFunctionToBalanceNewNat, hbalanceEq]

end UniswapV2Pair
