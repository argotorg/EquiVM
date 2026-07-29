import Examples.UniswapV2Pair.MintRuntimeFinalize
import Examples.UniswapV2Pair.MintInternalMintRuntime
import Examples.UniswapV2Pair.MintFeeSqrtSmall
import Examples.UniswapV2Pair.SyncCumulative

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

set_option maxHeartbeats 1000000 in
theorem uniswapMintFinishProportionalUpdateFirstBoundReverts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State} {mem outFee : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity toWord sel :
      UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (mintStore I) mintTransition.body .reverted)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfail0 : reserve112Mask.toNat < balance0.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapMintRuntimeAfterMintFeeProportionalUpdateFirstBoundReverts
      (liquidity := liquidity) rd3701 htotal htotalNonzero hclean0 hclean1
      hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero hperm
      htotalFit hbalanceFit hfail0 hmem hmem64
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintFinishProportionalUpdateSecondBoundReverts
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State} {mem outFee : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity toWord sel :
      UInt256}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (mintStore I) mintTransition.body .reverted)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord mem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfail1 : reserve112Mask.toNat < balance1.toNat)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapMintRuntimeAfterMintFeeProportionalUpdateSecondBoundReverts
      (liquidity := liquidity) rd3701 htotal htotalNonzero hclean0 hclean1
      hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero hperm
      htotalFit hbalanceFit hfit0 hfail1 hmem hmem64
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintFinishProportionalFeeOffCumulative
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State} {mem outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity sel feeOn :
      UInt256}
    {frame : Frame}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (mintStore I) mintTransition.body
        (.returned frame
          (uniswapLockExitedState
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evmFeeS
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1 reserve0 reserve1))
          (some [uniswapUint256Value liquidity])))
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOn, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem)).toNat +
          liquidity.toNat <
        UInt256.size)
    (hfitSupplySource : mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size)
    (hbalanceFitSource :
      mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsedNe :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask ≠ ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let postMint :=
    mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat) liquidity
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
      (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
        (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
  have hMintAccounts : accountMapEquiv σAfterMint postMint.accountMap := by
    simpa [postMint, σAfterMint, htotal] using
      accountMapEquiv_mintFunctionPostState_of_runtimeMint
        hPostAccountsFee henvFeeI (by rw [hmem]; omega)
        hfitSupplySource hbalanceFitSource
  have henvMint : postMint.executionEnv = I := by
    simp [postMint, mintFunctionPostState, mintFunctionAfterTotalSupplyState, henvFeeI,
      storageStore_executionEnv]
  have hslot8 :
      Solm.EVM.storageLoad postMint postMint.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σAfterMint I := by
    have hword := accountMapEquiv_storage_findD hMintAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    simpa [postMint, uniswapSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, henvMint] using hword.symm
  have hreserve0Lt : reserve0.toNat < 2 ^ 112 := by
    rw [← hclean0]
    simpa [u256_land_comm] using uniswapUint112Masked_lt reserve0
  have hreserve1Lt : reserve1.toNat < 2 ^ 112 := by
    rw [← hclean1]
    simpa [u256_land_comm] using uniswapUint112Masked_lt reserve1
  have hAccountsRet :
      accountMapEquiv
        (uniswapUpdateCumulativeReturnMapWith σAfterMint I balance0 balance1 reserve0 reserve1)
        (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveStateWith
            postMint balance0 balance1 reserve0 reserve1)).accountMap :=
    accountMapEquiv_syncUpdateCumulativeReturnMapWith hMintAccounts henvMint hslot8
      hreserve0Lt hreserve1Lt
  have hCreatedRet :
      cAFee =
        (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveStateWith
            postMint balance0 balance1 reserve0 reserve1)).createdAccounts := by
    simp [uniswapLockExitedState, uniswapUnlockedState, syncUpdateCumulativePackedReserveStateWith,
      postMint, syncUpdatePackedReserveState, mintFunctionPostState,
      mintFunctionAfterTotalSupplyState, storageStore_createdAccounts, hcreatedFee]
  have rdRet :
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee,
          uniswapUpdateCumulativeReturnMapWith σAfterMint I balance0 balance1 reserve0 reserve1)
        (UInt256.toByteArray liquidity) := by
    simpa [σAfterMint, htotal] using
      uniswapMintRuntimeAfterMintFeeProportionalUpdateCumulativeFeeOffReturns
        (liquidity := liquidity) rd3701 htotal htotalNonzero hclean0 hclean1
        hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero
        hperm htotalFit hbalanceFit hbound0 hbound1 helapsedNe hfeeOff hmem hmem64
  exact rdRet.reEquivExecutionGenAccountMapEquiv
    hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody hCreatedRet hAccountsRet
    (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding liquidity))

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 100000000 in
theorem uniswapMintFinishProportionalFeeOnCumulativeKLastUpdated
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State} {mem outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity sel : UInt256}
    {frame : Frame}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (mintStore I) mintTransition.body
        (.returned frame
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdateCumulativePackedReserveStateWith
                (mintFunctionPostState evmFeeS
                  (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
                balance0 balance1 reserve0 reserve1)))
          (some [uniswapUint256Value liquidity])))
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem)).toNat +
          liquidity.toNat <
        UInt256.size)
    (hfitSupplySource : mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size)
    (hbalanceFitSource :
      mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsedNe :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask ≠ ⟨0⟩)
    (hfitKLast :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
      (UInt256.land
            (uniswapSlotWord ⟨8⟩
              (uniswapUpdateCumulativePackedMapWith
                σAfterMint I balance0 balance1 reserve0 reserve1) I)
            reserve112Mask).toNat *
          (UInt256.land
            (UInt256.div
              (uniswapSlotWord ⟨8⟩
                (uniswapUpdateCumulativePackedMapWith
                  σAfterMint I balance0 balance1 reserve0 reserve1) I)
              reserve112Shift)
            reserve112Mask).toNat <
        UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let postMint :=
    mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat) liquidity
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
      (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
        (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
  let σCumulative :=
    uniswapUpdateCumulativePackedMapWith σAfterMint I balance0 balance1 reserve0 reserve1
  let syncState :=
    syncUpdateCumulativePackedReserveStateWith postMint balance0 balance1 reserve0 reserve1
  let kLastWord :=
    UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σCumulative I) reserve112Mask)
      (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σCumulative I) reserve112Shift)
        reserve112Mask)
  have hMintAccounts : accountMapEquiv σAfterMint postMint.accountMap := by
    simpa [postMint, σAfterMint, htotal] using
      accountMapEquiv_mintFunctionPostState_of_runtimeMint
        hPostAccountsFee henvFeeI (by rw [hmem]; omega)
        hfitSupplySource hbalanceFitSource
  have henvMint : postMint.executionEnv = I := by
    simp [postMint, mintFunctionPostState, mintFunctionAfterTotalSupplyState, henvFeeI,
      storageStore_executionEnv]
  have hslot8 :
      Solm.EVM.storageLoad postMint postMint.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σAfterMint I := by
    have hword := accountMapEquiv_storage_findD hMintAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    simpa [postMint, uniswapSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, henvMint] using hword.symm
  have hreserve0Lt : reserve0.toNat < 2 ^ 112 := by
    rw [← hclean0]
    simpa [u256_land_comm] using uniswapUint112Masked_lt reserve0
  have hreserve1Lt : reserve1.toNat < 2 ^ 112 := by
    rw [← hclean1]
    simpa [u256_land_comm] using uniswapUint112Masked_lt reserve1
  let evmP0 :=
    Solm.EVM.storageStore postMint I.codeOwner ⟨9⟩
      (EVM.wordOfInt (syncPrice0CumulativeIntAtWith postMint postMint reserve0 reserve1))
  let evmP1 :=
    Solm.EVM.storageStore evmP0 I.codeOwner ⟨10⟩
      (EVM.wordOfInt (syncPrice1CumulativeIntAtWith evmP0 postMint reserve0 reserve1))
  let σP1 : AccountMap := uniswapUpdatePrice1CumulativeMapWith σAfterMint I reserve0 reserve1
  let packedCumulative : UInt256 :=
    uniswapUpdateCumulativePackedWordWith σAfterMint I balance0 balance1 reserve0 reserve1
  have hP1Accounts : accountMapEquiv σP1 evmP1.accountMap := by
    simpa [σP1, evmP0, evmP1] using
      accountMapEquiv_uniswapUpdatePrice1CumulativeMapWith hMintAccounts henvMint hslot8
        hreserve0Lt hreserve1Lt
  have henvP0 : evmP0.executionEnv = I := by
    simp [evmP0, storageStore_executionEnv, henvMint]
  have henvP1 : evmP1.executionEnv = I := by
    simp [evmP1, storageStore_executionEnv, henvP0]
  have hslot8P1 :
      Solm.EVM.storageLoad evmP1 evmP1.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σP1 I := by
    have h := accountMapEquiv_storage_findD hP1Accounts I.codeOwner ⟨8⟩ ⟨0⟩
    simp [Solm.EVM.storageLoad, State.lookupAccount, Account.lookupStorage,
      uniswapSlotWord, henvP1] at h ⊢
    exact h.symm
  have hPackedAccountsStep :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σP1 ⟨8⟩ packedCumulative)
        (syncUpdatePackedReserveState evmP1 balance0 balance1).accountMap :=
    accountMapEquiv_syncUpdatePackedReserveState hP1Accounts henvP1 hslot8P1
      (by simp [packedCumulative, uniswapUpdateCumulativePackedWordWith, σP1])
  have hPackedAccounts : accountMapEquiv σCumulative syncState.accountMap := by
    simpa [σCumulative, syncState, uniswapUpdateCumulativePackedMapWith,
      uniswapUpdateCumulativePackedWordWith, syncUpdateCumulativePackedReserveStateWith,
      syncUpdatePackedReserveState, evmP0, evmP1, σP1, packedCumulative,
      storageStore_executionEnv, henvMint, henvP0] using hPackedAccountsStep
  have henvSync : syncState.executionEnv = I := by
    simp [syncState, syncUpdateCumulativePackedReserveStateWith, syncUpdatePackedReserveState,
      postMint, henvMint, storageStore_executionEnv]
  have hslot8Sync :
      Solm.EVM.storageLoad syncState syncState.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σCumulative I := by
    have hword := accountMapEquiv_storage_findD hPackedAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    simpa [syncState, uniswapSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, henvSync] using hword.symm
  have hsyncReserve0 :
      uniswapReserve0Word syncState =
        UInt256.land (uniswapSlotWord ⟨8⟩ σCumulative I) reserve112Mask := by
    simp [uniswapReserve0Word, hslot8Sync]
  have hsyncReserve1 :
      uniswapReserve1Word syncState =
        UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σCumulative I) reserve112Shift)
          reserve112Mask := by
    simp [uniswapReserve1Word, hslot8Sync]
  have hkLastValue :
      mintFeeReserveProductWord (uniswapReserve0Word syncState)
          (uniswapReserve1Word syncState) =
        kLastWord := by
    rw [hsyncReserve0, hsyncReserve1]
    dsimp [kLastWord]
    exact mintFeeReserveProductWord_eq_mul _ _ (by
      simpa [mintFeeReserveProductNat, σAfterMint, σCumulative] using hfitKLast)
  have hKLastAccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σCumulative ⟨11⟩ kLastWord)
        (mintKLastUpdatedState syncState).accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ kLastWord
      hPackedAccounts
    simpa [mintKLastUpdatedState, storageStore_accountMap, henvSync, hkLastValue] using hs
  have hAccountsRet :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σCumulative ⟨11⟩ kLastWord) ⟨12⟩
          (⟨1⟩ : UInt256))
        (uniswapLockExitedState (mintKLastUpdatedState syncState)).accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hKLastAccounts
    simpa [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap,
      storageStore_executionEnv, mintKLastUpdatedState, henvSync] using hs
  have hCreatedRet :
      cAFee = (uniswapLockExitedState (mintKLastUpdatedState syncState)).createdAccounts := by
    simp [uniswapLockExitedState, uniswapUnlockedState, mintKLastUpdatedState, syncState,
      postMint, syncUpdateCumulativePackedReserveStateWith, syncUpdatePackedReserveState,
      mintFunctionPostState, mintFunctionAfterTotalSupplyState, storageStore_createdAccounts,
      hcreatedFee]
  have rdRet :
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σCumulative ⟨11⟩ kLastWord) ⟨12⟩
          (⟨1⟩ : UInt256))
        (UInt256.toByteArray liquidity) := by
    simpa [σAfterMint, σCumulative, kLastWord, htotal] using
      uniswapMintRuntimeAfterMintFeeProportionalUpdateCumulativeFeeOnReturns
        (liquidity := liquidity) rd3701 htotal htotalNonzero hclean0 hclean1
        hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero
        hperm htotalFit hbalanceFit hbound0 hbound1 helapsedNe
        (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hfitKLast hmem hmem64
  exact rdRet.reEquivExecutionGenAccountMapEquiv
    hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody hCreatedRet hAccountsRet
    (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding liquidity))

set_option maxHeartbeats 1000000 in
theorem uniswapMintFinishProportionalFeeOnKLastUpdated
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmFeeS : EVM.State} {mem outFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity sel : UInt256}
    {frame : Frame}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (mintStore I) mintTransition.body
        (.returned frame
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmFeeS
                  (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
                balance0 balance1)))
          (some [uniswapUint256Value liquidity])))
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
    (htotal : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (htotalFit : (uniswapSlotWord ⟨0⟩ σFee I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem)).toNat +
          liquidity.toNat <
        UInt256.size)
    (hfitSupplySource : mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size)
    (hbalanceFitSource :
      mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfitKLast :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat <
        UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let postMint :=
    mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat) liquidity
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
      (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
        (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) mem) + liquidity)
  let packed :=
    uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
  let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
  let syncState := syncUpdatePackedReserveState postMint balance0 balance1
  let kLastWord :=
    UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask)
      (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
        reserve112Mask)
  have hMintAccounts : accountMapEquiv σAfterMint postMint.accountMap := by
    simpa [postMint, σAfterMint, htotal] using
      accountMapEquiv_mintFunctionPostState_of_runtimeMint
        hPostAccountsFee henvFeeI (by rw [hmem]; omega)
        hfitSupplySource hbalanceFitSource
  have henvMint : postMint.executionEnv = I := by
    simp [postMint, mintFunctionPostState, mintFunctionAfterTotalSupplyState, henvFeeI,
      storageStore_executionEnv]
  have hslot8 :
      Solm.EVM.storageLoad postMint postMint.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σAfterMint I := by
    have hword := accountMapEquiv_storage_findD hMintAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    simpa [postMint, uniswapSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, henvMint] using hword.symm
  have hPackedAccounts : accountMapEquiv σPacked syncState.accountMap := by
    exact accountMapEquiv_syncUpdatePackedReserveState hMintAccounts henvMint hslot8 rfl
  have henvSync : syncState.executionEnv = I := by
    simp [syncState, postMint, syncUpdatePackedReserveState, henvMint,
      storageStore_executionEnv]
  have hslot8Sync :
      Solm.EVM.storageLoad syncState syncState.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σPacked I := by
    have hword := accountMapEquiv_storage_findD hPackedAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    simpa [syncState, uniswapSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, henvSync] using hword.symm
  have hsyncReserve0 :
      uniswapReserve0Word syncState =
        UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask := by
    simp [uniswapReserve0Word, hslot8Sync]
  have hsyncReserve1 :
      uniswapReserve1Word syncState =
        UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
          reserve112Mask := by
    simp [uniswapReserve1Word, hslot8Sync]
  have hkLastValue :
      mintFeeReserveProductWord (uniswapReserve0Word syncState)
          (uniswapReserve1Word syncState) =
        kLastWord := by
    rw [hsyncReserve0, hsyncReserve1]
    dsimp [kLastWord]
    exact mintFeeReserveProductWord_eq_mul _ _ (by
      simpa [mintFeeReserveProductNat] using hfitKLast)
  have hKLastAccounts :
      accountMapEquiv (sstoreAccountMap I.codeOwner σPacked ⟨11⟩ kLastWord)
        (mintKLastUpdatedState syncState).accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨11⟩ kLastWord
      hPackedAccounts
    simpa [mintKLastUpdatedState, storageStore_accountMap, henvSync, hkLastValue] using hs
  have hAccountsRet :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σPacked ⟨11⟩ kLastWord) ⟨12⟩ (⟨1⟩ : UInt256))
        (uniswapLockExitedState (mintKLastUpdatedState syncState)).accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hKLastAccounts
    simpa [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap,
      storageStore_executionEnv, mintKLastUpdatedState, henvSync] using hs
  have hCreatedRet :
      cAFee = (uniswapLockExitedState (mintKLastUpdatedState syncState)).createdAccounts := by
    simp [uniswapLockExitedState, uniswapUnlockedState, mintKLastUpdatedState, syncState,
      postMint, syncUpdatePackedReserveState, mintFunctionPostState,
      mintFunctionAfterTotalSupplyState, storageStore_createdAccounts, hcreatedFee]
  have rdRet :
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σPacked ⟨11⟩ kLastWord) ⟨12⟩ (⟨1⟩ : UInt256))
        (UInt256.toByteArray liquidity) := by
    simpa [σAfterMint, packed, σPacked, kLastWord, htotal] using
      uniswapMintRuntimeAfterMintFeeProportionalFeeOnReturns
        (liquidity := liquidity) rd3701 htotal htotalNonzero hclean0 hclean1
        hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero hperm
        htotalFit hbalanceFit hbound0 hbound1 helapsed0
        (by decide : (⟨1⟩ : UInt256) ≠ ⟨0⟩) hfitKLast hmem hmem64
  exact rdRet.reEquivExecutionGenAccountMapEquiv
    hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody hCreatedRet hAccountsRet
    (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding liquidity))

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeOnKLastNonzeroNoMintCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {o o1 outFee memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity sel feeToWord :
      UInt256}
    {feeTo : AccountAddress} (rootK rootKLast : Int)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 :
      typedCallViaEVM config
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (EVM.address
          (uniswapAddressAtSlot
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
        "balanceOf" 0
        [.address
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
        (true, evm0S, o) false)
    (hdec0 : config.externalABI.decode? "balanceOf" o = some [uniswapUint256Value balance0])
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" o1 = some [uniswapUint256Value balance1])
    (hle0Source :
      (uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          feeTo true (mintFeeKLastWord evmFeeS))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame
            (uniswapReserve0Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            (uniswapReserve1Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            feeTo true (mintFeeKLastWord evmFeeS) rootK rootKLast)
          evmFeeS))
    (hrootNoMint : ¬ rootK > rootKLast)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (htotalFit : totalSupply.toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee)).toNat +
          liquidity.toNat <
        UInt256.size)
    (hbalanceFitSource :
      mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity <
        UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      UInt256.land (uniswapUpdateElapsedWord
        (uniswapSlotWord ⟨8⟩
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
              (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) memFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
              (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee) + liquidity))
          I) I) reserve32Mask = ⟨0⟩)
    (helapsedSource :
      syncTimeElapsedInt
        (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity) = 0)
    (hfitKLastRuntime :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) memFee))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat <
        UInt256.size)
    (hfitKLastSource :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1)) < UInt256.size)
    (hmem : memFee.size = 164)
    (hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeTo]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32)
      (by simpa [hfeeToWord] using hfeeToNonzero)
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have htotalSourceNonzero : mintFunctionTotalSupplyWord evmFeeS ≠ ⟨0⟩ := by
    intro hzero
    exact htotalNonzero (htotalEq.symm.trans hzero)
  have hfitSource0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evmS) balance0)
          (mintFunctionTotalSupplyWord evmFeeS) <
        UInt256.size := by
    simpa [evmS, mintAmountProductNat, hamount0, htotalEq] using hmulFit0
  have hfitSource1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evmS) balance1)
          (mintFunctionTotalSupplyWord evmFeeS) <
        UInt256.size := by
    simpa [evmS, mintAmountProductNat, hamount1, htotalEq] using hmulFit1
  have hreserve0Source : uniswapReserve0Word (uniswapLockEnteredState evmS) ≠ ⟨0⟩ := by
    intro hzero
    exact hreserve0Nonzero (hreserve0Eq.symm.trans (by simpa [evmS] using hzero))
  have hreserve1Source : uniswapReserve1Word (uniswapLockEnteredState evmS) ≠ ⟨0⟩ := by
    intro hzero
    exact hreserve1Nonzero (hreserve1Eq.symm.trans (by simpa [evmS] using hzero))
  have hprod0 :
      mintAmountProductWord amount0 totalSupply = UInt256.mul amount0 totalSupply :=
    mintAmountProductWord_eq_mul amount0 totalSupply hmulFit0
  have hprod1 :
      mintAmountProductWord amount1 totalSupply = UInt256.mul amount1 totalSupply :=
    mintAmountProductWord_eq_mul amount1 totalSupply hmulFit1
  have hliquiditySource :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evmS) balance0)
            (mintFunctionTotalSupplyWord evmFeeS)
            (uniswapReserve0Word (uniswapLockEnteredState evmS)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evmS) balance1)
            (mintFunctionTotalSupplyWord evmFeeS)
            (uniswapReserve1Word (uniswapLockEnteredState evmS))) := by
    rw [show mintAmount0Word (uniswapLockEnteredState evmS) balance0 = amount0 by
      simpa [evmS] using hamount0]
    rw [show mintAmount1Word (uniswapLockEnteredState evmS) balance1 = amount1 by
      simpa [evmS] using hamount1]
    rw [show mintFunctionTotalSupplyWord evmFeeS = totalSupply by exact htotalEq]
    rw [show uniswapReserve0Word (uniswapLockEnteredState evmS) = reserve0 by
      simpa [evmS] using hreserve0Eq]
    rw [show uniswapReserve1Word (uniswapLockEnteredState evmS) = reserve1 by
      simpa [evmS] using hreserve1Eq]
    simp [hliquidity, mintProportionalLiquidityWord, hprod0, hprod1]
  have hfitSupplySource : mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size := by
    simpa [mintFunctionTotalSupplyNewNat, htotalEq] using htotalFit
  have hbound0Source : Int.ofNat balance0.toNat ≤ maxUint112 := by
    have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
    have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound0
    norm_num [maxUint112]
    exact_mod_cast hnat
  have hbound1Source : Int.ofNat balance1.toNat ≤ maxUint112 := by
    have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
    have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound1
    norm_num [maxUint112]
    exact_mod_cast hnat
  have hbody :=
    ExecFuncBody.execBlockRet
      (uniswapMintProportionalFeeOnReturn_kLastNonzeroNoMint evmS evm0S evm1S evmFeeS I
        feeTo rootK rootKLast (by simpa [evmS, initState] using hwv) hunlockedSolm
        hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard
        hfeeCall hfeeDec hfeeToAddr hkLastSource hprefix hrootNoMint htotalSourceNonzero
        hfitSource0 hfitSource1 hreserve0Source hreserve1Source hliquiditySource
        hliqNonzero hfitSupplySource hbalanceFitSource hbound0Source hbound1Source
        helapsedSource hfitKLastSource)
  exact uniswapMintFinishProportionalFeeOnKLastUpdated hcode hdispatch hsz36 hbody rd3701
    hPostAccountsFee henvFeeI hcreatedFee htotalSlot htotalNonzero hclean0 hclean1 hmulFit0
    hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero hperm
    (by simpa [htotalSlot] using htotalFit)
    (by simpa [htotalSlot] using hbalanceFit)
    hfitSupplySource hbalanceFitSource hbound0 hbound1
    (by simpa [htotalSlot] using helapsed0)
    (by simpa [htotalSlot] using hfitKLastRuntime)
    hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeOnKLastNonzeroPositiveNoLiquidityCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {o o1 outFee memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity sel feeToWord :
      UInt256}
    {feeTo : AccountAddress} (rootK rootKLast : Int)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 :
      typedCallViaEVM config
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (EVM.address
          (uniswapAddressAtSlot
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
        "balanceOf" 0
        [.address
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
        (true, evm0S, o) false)
    (hdec0 : config.externalABI.decode? "balanceOf" o = some [uniswapUint256Value balance0])
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" o1 = some [uniswapUint256Value balance1])
    (hle0Source :
      (uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          feeTo true (mintFeeKLastWord evmFeeS))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame
            (uniswapReserve0Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            (uniswapReserve1Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            feeTo true (mintFeeKLastWord evmFeeS) rootK rootKLast)
          evmFeeS))
    (hroot : rootK > rootKLast)
    (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hfeeLiq : ¬ mintFeeLiquidityInt evmFeeS rootK rootKLast > 0)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (htotalFit : totalSupply.toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee)).toNat +
          liquidity.toNat <
        UInt256.size)
    (hbalanceFitSource :
      mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity <
        UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      UInt256.land (uniswapUpdateElapsedWord
        (uniswapSlotWord ⟨8⟩
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
              (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) memFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
              (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee) + liquidity))
          I) I) reserve32Mask = ⟨0⟩)
    (helapsedSource :
      syncTimeElapsedInt
        (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity) = 0)
    (hfitKLastRuntime :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) memFee))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat <
        UInt256.size)
    (hfitKLastSource :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1)) < UInt256.size)
    (hmem : memFee.size = 164)
    (hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeTo]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32)
      (by simpa [hfeeToWord] using hfeeToNonzero)
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have htotalSourceNonzero : mintFunctionTotalSupplyWord evmFeeS ≠ ⟨0⟩ := by
    intro hzero
    exact htotalNonzero (htotalEq.symm.trans hzero)
  have hfitSource0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evmS) balance0)
          (mintFunctionTotalSupplyWord evmFeeS) <
        UInt256.size := by
    simpa [evmS, mintAmountProductNat, hamount0, htotalEq] using hmulFit0
  have hfitSource1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evmS) balance1)
          (mintFunctionTotalSupplyWord evmFeeS) <
        UInt256.size := by
    simpa [evmS, mintAmountProductNat, hamount1, htotalEq] using hmulFit1
  have hreserve0Source : uniswapReserve0Word (uniswapLockEnteredState evmS) ≠ ⟨0⟩ := by
    intro hzero
    exact hreserve0Nonzero (hreserve0Eq.symm.trans (by simpa [evmS] using hzero))
  have hreserve1Source : uniswapReserve1Word (uniswapLockEnteredState evmS) ≠ ⟨0⟩ := by
    intro hzero
    exact hreserve1Nonzero (hreserve1Eq.symm.trans (by simpa [evmS] using hzero))
  have hprod0 :
      mintAmountProductWord amount0 totalSupply = UInt256.mul amount0 totalSupply :=
    mintAmountProductWord_eq_mul amount0 totalSupply hmulFit0
  have hprod1 :
      mintAmountProductWord amount1 totalSupply = UInt256.mul amount1 totalSupply :=
    mintAmountProductWord_eq_mul amount1 totalSupply hmulFit1
  have hliquiditySource :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evmS) balance0)
            (mintFunctionTotalSupplyWord evmFeeS)
            (uniswapReserve0Word (uniswapLockEnteredState evmS)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evmS) balance1)
            (mintFunctionTotalSupplyWord evmFeeS)
            (uniswapReserve1Word (uniswapLockEnteredState evmS))) := by
    rw [show mintAmount0Word (uniswapLockEnteredState evmS) balance0 = amount0 by
      simpa [evmS] using hamount0]
    rw [show mintAmount1Word (uniswapLockEnteredState evmS) balance1 = amount1 by
      simpa [evmS] using hamount1]
    rw [show mintFunctionTotalSupplyWord evmFeeS = totalSupply by exact htotalEq]
    rw [show uniswapReserve0Word (uniswapLockEnteredState evmS) = reserve0 by
      simpa [evmS] using hreserve0Eq]
    rw [show uniswapReserve1Word (uniswapLockEnteredState evmS) = reserve1 by
      simpa [evmS] using hreserve1Eq]
    simp [hliquidity, mintProportionalLiquidityWord, hprod0, hprod1]
  have hfitSupplySource : mintFunctionTotalSupplyNewNat evmFeeS liquidity < UInt256.size := by
    simpa [mintFunctionTotalSupplyNewNat, htotalEq] using htotalFit
  have hbound0Source : Int.ofNat balance0.toNat ≤ maxUint112 := by
    have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
    have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound0
    norm_num [maxUint112]
    exact_mod_cast hnat
  have hbound1Source : Int.ofNat balance1.toNat ≤ maxUint112 := by
    have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
    have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound1
    norm_num [maxUint112]
    exact_mod_cast hnat
  have hbody :=
    ExecFuncBody.execBlockRet
      (uniswapMintProportionalFeeOnReturn_kLastNonzeroPositiveNoLiquidity
        evmS evm0S evm1S evmFeeS I feeTo rootK rootKLast
        (by simpa [evmS, initState] using hwv) hunlockedSolm hguard0 hguard1 hcall0
        hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
        hfeeToAddr hkLastSource hprefix hroot hrootKNonneg hrootKSize
        hrootKLastNonneg hnumFit hrootFiveFit hdenFit hdenom hfeeLiq
        htotalSourceNonzero hfitSource0 hfitSource1 hreserve0Source hreserve1Source
        hliquiditySource hliqNonzero hfitSupplySource hbalanceFitSource hbound0Source
        hbound1Source helapsedSource hfitKLastSource)
  exact uniswapMintFinishProportionalFeeOnKLastUpdated hcode hdispatch hsz36 hbody rd3701
    hPostAccountsFee henvFeeI hcreatedFee htotalSlot htotalNonzero hclean0 hclean1 hmulFit0
    hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero hperm
    (by simpa [htotalSlot] using htotalFit)
    (by simpa [htotalSlot] using hbalanceFit)
    hfitSupplySource hbalanceFitSource hbound0 hbound1
    (by simpa [htotalSlot] using helapsed0)
    (by simpa [htotalSlot] using hfitKLastRuntime)
    hmem hmem64

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeOnKLastNonzeroPositiveWithLiquidityCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee σAfterFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {o o1 outFee memFee memAfterFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity sel feeToWord :
      UInt256}
    {feeTo : AccountAddress} (rootK rootKLast : Int)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hσAfterFee :
      σAfterFee =
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + mintFeeLiquidityWord evmFeeS rootK rootKLast))
          (uniswapInternalMintBalanceHashSlot feeToWord
            (uniswapInternalMintBalanceHashMem feeToWord memFee))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + mintFeeLiquidityWord evmFeeS rootK rootKLast))
            (uniswapInternalMintBalanceHashSlot feeToWord memFee) +
              mintFeeLiquidityWord evmFeeS rootK rootKLast))
    (hmemAfterFee :
      memAfterFee =
        uniswapInternalMintLogMem (mintFeeLiquidityWord evmFeeS rootK rootKLast)
          (uniswapInternalMintBalanceHashMem feeToWord
            (uniswapInternalMintBalanceHashMem feeToWord memFee)))
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 :
      typedCallViaEVM config
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (EVM.address
          (uniswapAddressAtSlot
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
        "balanceOf" 0
        [.address
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
        (true, evm0S, o) false)
    (hdec0 : config.externalABI.decode? "balanceOf" o = some [uniswapUint256Value balance0])
    (hcall1 :
      typedCallViaEVM config evm0S (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩))
        "balanceOf" 0 [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" o1 = some [uniswapUint256Value balance1])
    (hle0Source :
      (uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall :
      typedCallViaEVM config evm1S (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩))
        "feeTo" 0 [] (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σAfterFee I = totalSupply)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          feeTo true (mintFeeKLastWord evmFeeS))
        evmFeeS
        [ .internalCall "sqrt" [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))]
            "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame
            (uniswapReserve0Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            (uniswapReserve1Word
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
            feeTo true (mintFeeKLastWord evmFeeS) rootK rootKLast)
          evmFeeS))
    (hroot : rootK > rootKLast)
    (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size)
    (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFeeS rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hfeeLiq : mintFeeLiquidityInt evmFeeS rootK rootKLast > 0)
    (hfeeLiqFit : (mintFeeLiquidityInt evmFeeS rootK rootKLast).toNat < UInt256.size)
    (hfeeFitSupply :
      mintFunctionTotalSupplyNewNat evmFeeS (mintFeeLiquidityWord evmFeeS rootK rootKLast) <
        UInt256.size)
    (hfeeFitBalance :
      mintFunctionToBalanceNewNat evmFeeS feeTo (mintFeeLiquidityWord evmFeeS rootK rootKLast) <
        UInt256.size)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      memAfterFee feeToStaticcallActiveWords outFee (cAFee, σAfterFee) k C)
    (hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (htotalFit : totalSupply.toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterFee ⟨0⟩ (totalSupply + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memAfterFee)).toNat +
          liquidity.toNat <
        UInt256.size)
    (hbalanceFitSource :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmFeeS feeTo (mintFeeLiquidityWord evmFeeS rootK rootKLast))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
        UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      UInt256.land (uniswapUpdateElapsedWord
        (uniswapSlotWord ⟨8⟩
          (sstoreAccountMap I.codeOwner
            (sstoreAccountMap I.codeOwner σAfterFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
              (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) memAfterFee))
            (uniswapCodeOwnerStorageWord I
              (sstoreAccountMap I.codeOwner σAfterFee ⟨0⟩ (totalSupply + liquidity))
              (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memAfterFee) +
                liquidity))
          I) I) reserve32Mask = ⟨0⟩)
    (helapsedSource :
      syncTimeElapsedInt
        (mintFunctionPostState
          (mintFunctionPostState evmFeeS feeTo (mintFeeLiquidityWord evmFeeS rootK rootKLast))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity) = 0)
    (hfitKLastRuntime :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterFee ⟨0⟩ (totalSupply + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) memAfterFee))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memAfterFee) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat <
        UInt256.size)
    (hfitKLastSource :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmFeeS feeTo
                  (mintFeeLiquidityWord evmFeeS rootK rootKLast))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmFeeS feeTo
                  (mintFeeLiquidityWord evmFeeS rootK rootKLast))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1)) < UInt256.size)
    (hmem : memFee.size = 164)
    (hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let feeLiquidity := mintFeeLiquidityWord evmFeeS rootK rootKLast
  let evmAfterFee := mintFunctionPostState evmFeeS feeTo feeLiquidity
  have hfeeToAddr : feeTo ≠ AccountAddress.ofNat 0 := by
    rw [hfeeTo]
    exact accountAddress_ofNat_ne_zero_of_land_solcAddrMask_ne_zero
      (fromByteArrayBigEndian_extract0_32_lt houtFee32)
      (by simpa [hfeeToWord] using hfeeToNonzero)
  have hkLastSource : (mintFeeKLastWord evmFeeS).toNat ≠ 0 := by
    intro hzero
    apply hkLastNonzero
    rw [← hkLastEq]
    exact uint256_toNat_eq_zero hzero
  have hPostAfterFee : accountMapEquiv σAfterFee evmAfterFee.accountMap := by
    have hraw :=
      accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient
        (σ := σFee) (evm := evmFeeS) (I := I) (mem := memFee)
        (liquidity := feeLiquidity) (recipientWord := feeToWord) (recipient := feeTo)
        hPostAccountsFee henvFeeI
        (by
          rw [hfeeTo, hfeeToWord,
            UInt256.toNat_ofNat_of_lt (fromByteArrayBigEndian_extract0_32_lt houtFee32)])
        (by rw [hmem]; omega)
        (by simpa [feeLiquidity] using hfeeFitSupply)
        (by simpa [feeLiquidity] using hfeeFitBalance)
    simpa [evmAfterFee, feeLiquidity, hσAfterFee] using hraw
  have henvAfterFee : evmAfterFee.executionEnv = I := by
    simp [evmAfterFee, feeLiquidity, mintFunctionPostState, mintFunctionAfterTotalSupplyState,
      henvFeeI, storageStore_executionEnv]
  have hcreatedAfterFee : evmAfterFee.createdAccounts = cAFee := by
    simp [evmAfterFee, feeLiquidity, mintFunctionPostState, mintFunctionAfterTotalSupplyState,
      storageStore_createdAccounts, hcreatedFee]
  have htotalEqAfterFee :
      mintFunctionTotalSupplyWord evmAfterFee = totalSupply := by
    have hslot :=
      mintFunctionTotalSupplyWord_eq_slot_of_accountMapEquiv hPostAfterFee henvAfterFee
    exact hslot.trans htotalSlot
  have htotalSourceNonzero : mintFunctionTotalSupplyWord evmAfterFee ≠ ⟨0⟩ := by
    intro hzero
    exact htotalNonzero (htotalEqAfterFee.symm.trans hzero)
  have hfitSource0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evmS) balance0)
          (mintFunctionTotalSupplyWord evmAfterFee) <
        UInt256.size := by
    simpa [evmS, mintAmountProductNat, hamount0, htotalEqAfterFee] using hmulFit0
  have hfitSource1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evmS) balance1)
          (mintFunctionTotalSupplyWord evmAfterFee) <
        UInt256.size := by
    simpa [evmS, mintAmountProductNat, hamount1, htotalEqAfterFee] using hmulFit1
  have hreserve0Source : uniswapReserve0Word (uniswapLockEnteredState evmS) ≠ ⟨0⟩ := by
    intro hzero
    exact hreserve0Nonzero (hreserve0Eq.symm.trans (by simpa [evmS] using hzero))
  have hreserve1Source : uniswapReserve1Word (uniswapLockEnteredState evmS) ≠ ⟨0⟩ := by
    intro hzero
    exact hreserve1Nonzero (hreserve1Eq.symm.trans (by simpa [evmS] using hzero))
  have hprod0 :
      mintAmountProductWord amount0 totalSupply = UInt256.mul amount0 totalSupply :=
    mintAmountProductWord_eq_mul amount0 totalSupply hmulFit0
  have hprod1 :
      mintAmountProductWord amount1 totalSupply = UInt256.mul amount1 totalSupply :=
    mintAmountProductWord_eq_mul amount1 totalSupply hmulFit1
  have hliquiditySource :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evmS) balance0)
            (mintFunctionTotalSupplyWord evmAfterFee)
            (uniswapReserve0Word (uniswapLockEnteredState evmS)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evmS) balance1)
            (mintFunctionTotalSupplyWord evmAfterFee)
            (uniswapReserve1Word (uniswapLockEnteredState evmS))) := by
    rw [show mintAmount0Word (uniswapLockEnteredState evmS) balance0 = amount0 by
      simpa [evmS] using hamount0]
    rw [show mintAmount1Word (uniswapLockEnteredState evmS) balance1 = amount1 by
      simpa [evmS] using hamount1]
    rw [show mintFunctionTotalSupplyWord evmAfterFee = totalSupply by exact htotalEqAfterFee]
    rw [show uniswapReserve0Word (uniswapLockEnteredState evmS) = reserve0 by
      simpa [evmS] using hreserve0Eq]
    rw [show uniswapReserve1Word (uniswapLockEnteredState evmS) = reserve1 by
      simpa [evmS] using hreserve1Eq]
    simp [hliquidity, mintProportionalLiquidityWord, hprod0, hprod1]
  have hfitSupplySource : mintFunctionTotalSupplyNewNat evmAfterFee liquidity < UInt256.size := by
    simpa [mintFunctionTotalSupplyNewNat, htotalEqAfterFee] using htotalFit
  have hbound0Source : Int.ofNat balance0.toNat ≤ maxUint112 := by
    have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
    have hnat : balance0.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound0
    norm_num [maxUint112]
    exact_mod_cast hnat
  have hbound1Source : Int.ofNat balance1.toNat ≤ maxUint112 := by
    have hmask : reserve112Mask.toNat = 2 ^ 112 - 1 := by native_decide
    have hnat : balance1.toNat ≤ 2 ^ 112 - 1 := by simpa [hmask] using hbound1
    norm_num [maxUint112]
    exact_mod_cast hnat
  have hbody :=
    ExecFuncBody.execBlockRet
      (uniswapMintProportionalFeeOnReturn_kLastNonzeroPositiveWithLiquidity
        evmS evm0S evm1S evmFeeS I feeTo rootK rootKLast
        (by simpa [evmS, initState] using hwv) hunlockedSolm hguard0 hguard1 hcall0
        hdec0 hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec
        hfeeToAddr hkLastSource hprefix hroot hrootKNonneg hrootKSize
        hrootKLastNonneg hnumFit hrootFiveFit hdenFit hdenom hfeeLiq hfeeLiqFit
        hfeeFitSupply hfeeFitBalance htotalSourceNonzero hfitSource0 hfitSource1
        hreserve0Source hreserve1Source hliquiditySource hliqNonzero hfitSupplySource
        hbalanceFitSource hbound0Source hbound1Source
        (by simpa [evmAfterFee, feeLiquidity] using helapsedSource)
        (by simpa [evmAfterFee, feeLiquidity] using hfitKLastSource))
  have hmemAfter : memAfterFee.size = 164 := by
    rw [hmemAfterFee]
    rw [uniswapInternalMintSuccessMem_size_of_ge160 feeToWord feeLiquidity (by
      rw [hmem]
      omega), hmem]
  have hmem64After :
      memAfterFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩ := by
    rw [hmemAfterFee]
    exact uniswapInternalMintSuccessMem_read64_of_ge160 feeToWord feeLiquidity
      (by rw [hmem]; omega) hmem64
  exact uniswapMintFinishProportionalFeeOnKLastUpdated hcode hdispatch hsz36 hbody rd3701
    hPostAfterFee henvAfterFee hcreatedAfterFee htotalSlot htotalNonzero hclean0 hclean1
    hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity hliqNonzero hperm
    (by simpa [htotalSlot] using htotalFit)
    (by simpa [htotalSlot] using hbalanceFit)
    hfitSupplySource hbalanceFitSource hbound0 hbound1
    (by simpa [htotalSlot] using helapsed0)
    (by simpa [htotalSlot] using hfitKLastRuntime)
    hmemAfter hmem64After

set_option maxHeartbeats 1000000 in
theorem uniswapMintFeeOnKLastNonzeroSmallNoMintCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {o o1 outFee memFee : ByteArray} {k C : ℕ}
    {amount0 amount1 balance0 balance1 reserve0 reserve1 totalSupply liquidity sel feeToWord :
      UInt256}
    {feeTo : AccountAddress}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hperm : I.perm = true)
    (hwv : I.weiValue = ⟨0⟩)
    (houtFee32 : 32 ≤ outFee.size)
    (hfeeToWord : feeToWord = UInt256.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hfeeTo : feeTo = AccountAddress.ofNat (fromByteArrayBigEndian (outFee.extract 0 32)))
    (hunlockedSolm :
      Solm.EVM.storageLoad
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I).executionEnv.codeOwner
          ⟨12⟩ =
        ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract,
          locals :=
            mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I }
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals :=
            (mintReserveStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I).insert
              "balance0" (uniswapUint256Value balance0) }
        evm0S (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) =
          .ok (.bool true))
    (hcall0 : typedCallViaEVM config
      (uniswapLockEnteredState
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))
      (EVM.address
        (uniswapAddressAtSlot
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) ⟨6⟩))
      "balanceOf" 0
      [.address
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)).executionEnv.codeOwner]
      (true, evm0S, o) false)
    (hdec0 : config.externalABI.decode? "balanceOf" o = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, o1) false)
    (hdec1 : config.externalABI.decode? "balanceOf" o1 = some [uniswapUint256Value balance1])
    (hle0Source :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance0.toNat)
    (hle1Source :
      (uniswapReserve1Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
        balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame
          (uniswapReserve0Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)))
          (uniswapReserve1Word
            (uniswapLockEnteredState
              (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))))
        evm1S (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1S
      (EVM.address (uniswapAddressAtSlot evm1S ⟨5⟩)) "feeTo" 0 []
      (true, evmFeeS, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hPostAccountsFee : accountMapEquiv σFee evmFeeS.accountMap)
    (henvFeeI : evmFeeS.executionEnv = I)
    (hcreatedFee : evmFeeS.createdAccounts = cAFee)
    (hreserve0Eq :
      uniswapReserve0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve0)
    (hreserve1Eq :
      uniswapReserve1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) =
        reserve1)
    (hamount0 :
      mintAmount0Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance0 =
        amount0)
    (hamount1 :
      mintAmount1Word
          (uniswapLockEnteredState
            (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) balance1 =
        amount1)
    (hkLastEq : mintFeeKLastWord evmFeeS = mintFeeKLastSlotWord σFee I)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [⟨1⟩, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        mintToMaskedWord I, ⟨861⟩, sel]
      memFee feeToStaticcallActiveWords outFee (cAFee, σFee) k C)
    (hfeeToNonzero : UInt256.land feeToWord solcAddrMask ≠ ⟨0⟩)
    (hkLastNonzero : mintFeeKLastSlotWord σFee I ≠ ⟨0⟩)
    (hrootLeRuntime :
      (if UInt256.mul reserve0 reserve1 = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat ≤
        (if mintFeeKLastSlotWord σFee I = ⟨0⟩ then (⟨0⟩ : UInt256) else ⟨1⟩).toNat)
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hprodSmall : (UInt256.mul reserve0 reserve1).toNat ≤ 3)
    (hkLastSmall : (mintFeeKLastSlotWord σFee I).toNat ≤ 3)
    (hmulFit0 : amount0.toNat * totalSupply.toNat < UInt256.size)
    (hmulFit1 : amount1.toNat * totalSupply.toNat < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (UInt256.div (UInt256.mul amount0 totalSupply) reserve0)
          (UInt256.div (UInt256.mul amount1 totalSupply) reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (htotalFit : totalSupply.toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
        (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee)).toNat +
          liquidity.toNat <
        UInt256.size)
    (hbalanceFitSource :
      mintFunctionToBalanceNewNat evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hbound1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) memFee))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (helapsedSource :
      syncTimeElapsedInt
        (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity) = 0)
    (hfitKLastRuntime :
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
          (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I)
            (uniswapInternalMintBalanceHashMem (mintToMaskedWord I) memFee))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩ (totalSupply + liquidity))
            (uniswapInternalMintBalanceHashSlot (mintToMaskedWord I) memFee) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat <
        UInt256.size)
    (hfitKLastSource :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFeeS (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1)) < UInt256.size)
    (hmem : memFee.size = 164)
    (hmem64 : memFee.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let rootK : Int := if UInt256.mul reserve0 reserve1 = ⟨0⟩ then 0 else 1
  let rootKLast : Int := if mintFeeKLastSlotWord σFee I = ⟨0⟩ then 0 else 1
  have hrootNoMint : ¬ rootK > rootKLast := by
    dsimp [rootK, rootKLast]
    by_cases hp : UInt256.mul reserve0 reserve1 = ⟨0⟩
    · by_cases hk : mintFeeKLastSlotWord σFee I = ⟨0⟩
      · simp [hp, hk]
      · simp [hp, hk]
    · by_cases hk : mintFeeKLastSlotWord σFee I = ⟨0⟩
      · exfalso
        have hbad : (⟨1⟩ : UInt256).toNat = 0 := by
          simpa [hp, hk] using hrootLeRuntime
        exact (by native_decide : (⟨1⟩ : UInt256).toNat ≠ 0) hbad
      · simp [hp, hk]
  have hprodFitSource :
      mintFeeReserveProductNat (uniswapReserve0Word (uniswapLockEnteredState evmS))
          (uniswapReserve1Word (uniswapLockEnteredState evmS)) <
        UInt256.size := by
    simpa [evmS, hreserve0Eq, hreserve1Eq] using
      mintFeeReserveProductNat_lt_of_clean reserve0 reserve1 hclean0 hclean1
  have hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame (uniswapReserve0Word (uniswapLockEnteredState evmS))
          (uniswapReserve1Word (uniswapLockEnteredState evmS)) feeTo true
          (mintFeeKLastWord evmFeeS))
        evmFeeS
        [ .internalCall "sqrt"
            [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame (uniswapReserve0Word (uniswapLockEnteredState evmS))
            (uniswapReserve1Word (uniswapLockEnteredState evmS)) feeTo true
            (mintFeeKLastWord evmFeeS) rootK rootKLast)
          evmFeeS) := by
    simpa [evmS, rootK, rootKLast, hreserve0Eq, hreserve1Eq, hkLastEq] using
      mintFeeSqrtPrefixSmall evmFeeS reserve0 reserve1 feeTo (mintFeeKLastWord evmFeeS)
        (by simpa [evmS, hreserve0Eq, hreserve1Eq] using hprodFitSource)
        hprodSmall
        (by simpa [hkLastEq] using hkLastSmall)
  exact uniswapMintFeeOnKLastNonzeroNoMintCase rootK rootKLast hcode hdispatch hsz36
    hperm hwv houtFee32 hfeeToWord hfeeTo hunlockedSolm hguard0 hguard1 hcall0 hdec0
    hcall1 hdec1 hle0Source hle1Source hfeeGuard hfeeCall hfeeDec hPostAccountsFee
    henvFeeI hcreatedFee hreserve0Eq hreserve1Eq hamount0 hamount1 hkLastEq htotalSlot
    htotalEq hprefix hrootNoMint rd3701 hfeeToNonzero hkLastNonzero htotalNonzero
    hclean0 hclean1 hmulFit0 hmulFit1 hreserve0Nonzero hreserve1Nonzero hliquidity
    hliqNonzero htotalFit hbalanceFit hbalanceFitSource hbound0 hbound1 helapsed0
    helapsedSource hfitKLastRuntime hfitKLastSource hmem hmem64
end UniswapV2Pair
