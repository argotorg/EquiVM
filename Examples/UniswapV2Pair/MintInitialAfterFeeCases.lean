import Examples.UniswapV2Pair.MintInitialRuntimeCases

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

namespace UniswapV2Pair

theorem uniswapMintInitialAfterMintFeeCases
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmFeeS : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOnFlag totalSupply amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel :
      UInt256}
    (nextLocals : Store) (recipient : AccountAddress) (fee : Bool)
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hwv : I.weiValue = ⟨0⟩)
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
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
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
      (true, evm0S, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0S
      (EVM.address (uniswapAddressAtSlot evm0S ⟨7⟩)) "balanceOf" 0
      [.address evm0S.executionEnv.codeOwner] (true, evm1S, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
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
    (hfee :
      ExecStmt config
        { contract := contract,
          locals :=
            mintAmountStore
              (uniswapLockEnteredState
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0 balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmFeeS))
    (rd3701 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨3701⟩
      [feeOnFlag, ⟨0⟩, amount1, amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩,
        toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (htotalBase : nextLocals.get? "totalSupply" = none)
    (hamount0 : nextLocals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : nextLocals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 : nextLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : nextLocals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (htotalEq : mintFunctionTotalSupplyWord evmFeeS = totalSupply)
    (htotalSlot : uniswapSlotWord ⟨0⟩ σFee I = totalSupply)
    (htotalZero : totalSupply = ⟨0⟩)
    (hclean0 : UInt256.land reserve0 reserve112Mask = reserve0)
    (hclean1 : UInt256.land reserve1 reserve112Mask = reserve1)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hAccounts : accountMapEquiv σFee evmFeeS.accountMap)
    (henv : evmFeeS.executionEnv = I)
    (hcreated : cAFee = evmFeeS.createdAccounts)
    (hrecipient : recipient = AccountAddress.ofNat toWord.toNat)
    (hto : nextLocals.get? "to" = some (.address recipient))
    (hflag : feeOnFlag = if fee then ⟨1⟩ else ⟨0⟩)
    (hfeeOnGet : nextLocals.get? "feeOn" = some (.bool fee))
    (hbalance0 : nextLocals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : nextLocals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0Base : nextLocals.get? "reserve0" = none)
    (hreserve1Base : nextLocals.get? "reserve1" = none)
    (hkLast : nextLocals.get? "kLast" = none)
    (hunlocked : nextLocals.get? "unlocked" = none)
    (hperm : I.perm = true) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  let locals := nextLocals.insert "_totalSupply" (uniswapUint256Value (⟨0⟩ : UInt256))
  have hprefix := uniswapMintAfterMintFeeTotalSupplyPrefix_of_call
    evmS evm0S evm1S evmFeeS I nextLocals hwv hunlockedSolm hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 hle0Source hle1Source hfee htotalBase
  have hruntime := uniswapMintInitialRuntimeCases (locals := locals) evmFeeS recipient fee
    rd3701 hAccounts henv hrecipient
    (by rw [store_get_ne _ _ (by decide), hto]) (htotalSlot.trans htotalZero)
    (store_get_self _ _ _)
    (by rw [store_get_ne _ _ (by decide), hamount0])
    (by rw [store_get_ne _ _ (by decide), hamount1])
    hflag
    (by rw [store_get_ne _ _ (by decide), hfeeOnGet])
    (by rw [store_get_ne _ _ (by decide), hbalance0])
    (by rw [store_get_ne _ _ (by decide), hbalance1])
    (by rw [store_get_ne _ _ (by decide), hreserve0])
    (by rw [store_get_ne _ _ (by decide), hreserve1])
    (by rw [store_get_ne _ _ (by decide), hreserve0Base])
    (by rw [store_get_ne _ _ (by decide), hreserve1Base])
    (by rw [store_get_ne _ _ (by decide), hkLast])
    (by rw [store_get_ne _ _ (by decide), hunlocked])
    hclean0 hclean1 hperm hmem hmem64
  rcases hruntime with ⟨htail, rdRev⟩ | ⟨liquidity, frameRet, evmRet, σRet, htail,
    hRetAccounts, hcreatedRet, rdRet⟩
  · have hbody : ExecTransitionBody config contract evmS (mintStore I)
        mintTransition.body .reverted := by
      apply ExecFuncBody.execBlockRevert
      have hthrough := execBlock_append hprefix (by
        simpa only [locals, htotalEq, htotalZero] using htail)
      simpa only [mintTransition, mintAfterLiquidityTailStmts, List.append_assoc] using hthrough
    exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody
  · have hbody : ExecTransitionBody config contract evmS (mintStore I)
        mintTransition.body (.returned frameRet evmRet (some [uniswapUint256Value liquidity])) := by
      apply ExecFuncBody.execBlockRet
      have hthrough := execBlock_append hprefix (by
        simpa only [locals, htotalEq, htotalZero] using htail)
      simpa only [mintTransition, mintAfterLiquidityTailStmts, List.append_assoc] using hthrough
    exact rdRet.reEquivExecutionGenAccountMapEquiv hcode hdispatch (uniswapDecode_mint_ok hsz36)
      hbody (hcreated.trans hcreatedRet.symm) hRetAccounts
      (returnEquiv_of_encode (by simpa only [uint256] using uint256ReturnEncoding liquidity))

end UniswapV2Pair

