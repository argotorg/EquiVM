import Examples.UniswapV2Pair.MintSourcePrefixes

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach Reasoning.Refinement

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapMintProportionalFeeOffReturn_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0)
    (htotalNonzero : mintFunctionTotalSupplyWord evmFee ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmFee liquidity < UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evmFee (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
        (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity) = 0) :
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmFee
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool false))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdatePackedReserveState (mintFunctionPostState evmFee recipient liquidity)
            balance0 balance1))
        (some (uniswapUint256Value liquidity))) := by
  intro evmL recipient amount0 amount1 totalSupply reserve0 reserve1 nextFrame
    afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOffReturn_of_call
    evm evm0 evm1 evmFee I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1 evmFee I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 false)
    (by simpa [totalSupply] using htotalNonzero)
    (by simpa [evmL, amount0, totalSupply] using hfit0)
    (by simpa [evmL, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by simpa [evmL, amount0, amount1, totalSupply, reserve0, reserve1] using hliquidity)
    hliqNonzero
    (by simpa [totalSupply] using hfitSupply)
    (by simpa [recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [recipient] using helapsed)

theorem uniswapMintProportionalFeeOffCumulativeReturn_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0)
    (htotalNonzero : mintFunctionTotalSupplyWord evmFee ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmFee liquidity < UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evmFee (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      0 < syncTimeElapsedInt
        (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity))
    (hreserve0Post :
      Int.ofNat (uniswapReserve0Word
        (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity)).toNat ≠ 0)
    (hreserve1Post :
      Int.ofNat (uniswapReserve1Word
        (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity)).toNat ≠ 0) :
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmFee
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool false))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveState
            (mintFunctionPostState evmFee recipient liquidity) balance0 balance1))
        (some (uniswapUint256Value liquidity))) := by
  intro evmL recipient amount0 amount1 totalSupply reserve0 reserve1 nextFrame
    afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOffCumulativeReturn_of_call
    evm evm0 evm1 evmFee I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1 evmFee I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 false)
    (by simpa [totalSupply] using htotalNonzero)
    (by simpa [evmL, amount0, totalSupply] using hfit0)
    (by simpa [evmL, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by simpa [evmL, amount0, amount1, totalSupply, reserve0, reserve1] using hliquidity)
    hliqNonzero
    (by simpa [totalSupply] using hfitSupply)
    (by simpa [recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [recipient] using helapsed)
    (by simpa [recipient] using hreserve0Post)
    (by simpa [recipient] using hreserve1Post)

theorem uniswapMintProportionalFeeOnReturn_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0)
    (htotalNonzero : mintFunctionTotalSupplyWord evmFee ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmFee liquidity < UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evmFee (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
        (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity) = 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1)) < UInt256.size) :
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmFee
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool true))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState (mintFunctionPostState evmFee recipient liquidity)
              balance0 balance1)))
        (some (uniswapUint256Value liquidity))) := by
  intro evmL recipient amount0 amount1 totalSupply reserve0 reserve1 nextFrame
    afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOnReturn_of_call
    evm evm0 evm1 evmFee I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1 evmFee I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_kLast evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 true)
    (by simpa [totalSupply] using htotalNonzero)
    (by simpa [evmL, amount0, totalSupply] using hfit0)
    (by simpa [evmL, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by simpa [evmL, amount0, amount1, totalSupply, reserve0, reserve1] using hliquidity)
    hliqNonzero
    (by simpa [totalSupply] using hfitSupply)
    (by simpa [recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [recipient] using helapsed)
    (by simpa [recipient] using hfitKLast)

theorem uniswapMintProportionalFeeOnCumulativeReturn_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0)
    (htotalNonzero : mintFunctionTotalSupplyWord evmFee ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmFee liquidity < UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evmFee (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      0 <
        syncTimeElapsedInt
          (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
            liquidity))
    (hreserve0Post :
      Int.ofNat
          (uniswapReserve0Word
            (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
              liquidity)).toNat ≠
        0)
    (hreserve1Post :
      Int.ofNat
          (uniswapReserve1Word
            (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
              liquidity)).toNat ≠
        0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdateCumulativePackedReserveState
              (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdateCumulativePackedReserveState
              (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1)) < UInt256.size) :
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmFee
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool true))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdateCumulativePackedReserveState
              (mintFunctionPostState evmFee recipient liquidity) balance0 balance1)))
        (some (uniswapUint256Value liquidity))) := by
  intro evmL recipient amount0 amount1 totalSupply reserve0 reserve1 nextFrame
    afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOnCumulativeReturn_of_call
    evm evm0 evm1 evmFee I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1 evmFee I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_kLast evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 true)
    (by simpa [totalSupply] using htotalNonzero)
    (by simpa [evmL, amount0, totalSupply] using hfit0)
    (by simpa [evmL, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by simpa [evmL, amount0, amount1, totalSupply, reserve0, reserve1] using hliquidity)
    hliqNonzero
    (by simpa [totalSupply] using hfitSupply)
    (by simpa [recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [recipient] using helapsed)
    (by simpa [recipient] using hreserve0Post)
    (by simpa [recipient] using hreserve1Post)
    (by simpa [recipient] using hfitKLast)

theorem uniswapMintProportionalFeeOffReturn_kLastNonzero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (htotalNonzero : mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee) ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee)) < UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
        (mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee)) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee))
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee))
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFee) liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat (mintFeeKLastClearedState evmFee)
        (AccountAddress.ofNat (mintToWord I).toNat) liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
        (mintFunctionPostState (mintFeeKLastClearedState evmFee)
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity) = 0) :
    let evmL := uniswapLockEnteredState evm
    let evmAfter := mintFeeKLastClearedState evmFee
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmAfter
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool false))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdatePackedReserveState
            (mintFunctionPostState evmAfter recipient liquidity) balance0 balance1))
        (some (uniswapUint256Value liquidity))) := by
  intro evmL evmAfter recipient amount0 amount1 totalSupply reserve0 reserve1 nextFrame
    afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOffReturn_of_call
    evm evm0 evm1 evmAfter I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, evmAfter, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1 evmFee I balance0
          balance1 feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo
          hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 false)
    (by simpa [evmAfter, totalSupply] using htotalNonzero)
    (by simpa [evmL, evmAfter, amount0, totalSupply] using hfit0)
    (by simpa [evmL, evmAfter, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by
      simpa [evmL, evmAfter, amount0, amount1, totalSupply, reserve0, reserve1] using
        hliquidity)
    hliqNonzero
    (by simpa [evmAfter] using hfitSupply)
    (by simpa [evmAfter, recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [evmAfter, recipient] using helapsed)

theorem uniswapMintProportionalFeeOffCumulativeReturn_kLastNonzero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (htotalNonzero : mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee) ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee)) < UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
        (mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee)) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee))
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee))
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat (mintFeeKLastClearedState evmFee) liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat (mintFeeKLastClearedState evmFee)
        (AccountAddress.ofNat (mintToWord I).toNat) liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      0 <
        syncTimeElapsedInt
          (mintFunctionPostState (mintFeeKLastClearedState evmFee)
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity))
    (hreserve0Post :
      Int.ofNat
          (uniswapReserve0Word
            (mintFunctionPostState (mintFeeKLastClearedState evmFee)
              (AccountAddress.ofNat (mintToWord I).toNat) liquidity)).toNat ≠
        0)
    (hreserve1Post :
      Int.ofNat
          (uniswapReserve1Word
            (mintFunctionPostState (mintFeeKLastClearedState evmFee)
              (AccountAddress.ofNat (mintToWord I).toNat) liquidity)).toNat ≠
        0) :
    let evmL := uniswapLockEnteredState evm
    let evmAfter := mintFeeKLastClearedState evmFee
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmAfter
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool false))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveState
            (mintFunctionPostState evmAfter recipient liquidity) balance0 balance1))
        (some (uniswapUint256Value liquidity))) := by
  intro evmL evmAfter recipient amount0 amount1 totalSupply reserve0 reserve1 nextFrame
    afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOffCumulativeReturn_of_call
    evm evm0 evm1 evmAfter I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, evmAfter, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1 evmFee I balance0
          balance1 feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo
          hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 false)
    (by simpa [evmAfter, totalSupply] using htotalNonzero)
    (by simpa [evmL, evmAfter, amount0, totalSupply] using hfit0)
    (by simpa [evmL, evmAfter, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by
      simpa [evmL, evmAfter, amount0, amount1, totalSupply, reserve0, reserve1] using
        hliquidity)
    hliqNonzero
    (by simpa [evmAfter] using hfitSupply)
    (by simpa [evmAfter, recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [evmAfter, recipient] using helapsed)
    (by simpa [evmAfter, recipient] using hreserve0Post)
    (by simpa [evmAfter, recipient] using hreserve1Post)

theorem uniswapMintProportionalFeeOnReturn_kLastNonzeroNoMint
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress) (rootK rootKLast : Int)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)) feeTo true
          (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt"
            [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
            (uniswapReserve1Word (uniswapLockEnteredState evm)) feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee))
    (hroot : ¬ rootK > rootKLast)
    (htotalNonzero : mintFunctionTotalSupplyWord evmFee ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmFee liquidity < UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evmFee (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
        (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity) = 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1)) < UInt256.size) :
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmFee
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool true))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState (mintFunctionPostState evmFee recipient liquidity)
              balance0 balance1)))
        (some (uniswapUint256Value liquidity))) := by
  intro evmL recipient amount0 amount1 totalSupply reserve0 reserve1 nextFrame
    afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOnReturn_of_call
    evm evm0 evm1 evmFee I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOn_kLastNonzero_noMint evmL evm1 evmFee I balance0
          balance1 feeTo rootK rootKLast (by simpa [evmL] using hfeeGuard) hfeeCall
          hfeeDec hfeeTo hkLast (by simpa [evmL] using hprefix) hroot)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_kLast evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 true)
    (by simpa [totalSupply] using htotalNonzero)
    (by simpa [evmL, amount0, totalSupply] using hfit0)
    (by simpa [evmL, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by simpa [evmL, amount0, amount1, totalSupply, reserve0, reserve1] using hliquidity)
    hliqNonzero
    (by simpa [totalSupply] using hfitSupply)
    (by simpa [recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [recipient] using helapsed)
    (by simpa [recipient] using hfitKLast)

theorem uniswapMintProportionalFeeOnReturn_kLastNonzeroPositiveNoLiquidity
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress) (rootK rootKLast : Int)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)) feeTo true
          (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt"
            [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
            (uniswapReserve1Word (uniswapLockEnteredState evm)) feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee))
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFee rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hfeeLiq : ¬ mintFeeLiquidityInt evmFee rootK rootKLast > 0)
    (htotalNonzero : mintFunctionTotalSupplyWord evmFee ≠ ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
        (mintFunctionTotalSupplyWord evmFee) < UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord evmFee)
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evmFee liquidity < UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evmFee (AccountAddress.ofNat (mintToWord I).toNat)
        liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
        (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
          liquidity) = 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmFee (AccountAddress.ofNat (mintToWord I).toNat)
                liquidity)
              balance0 balance1)) < UInt256.size) :
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmFee
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool true))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState (mintFunctionPostState evmFee recipient liquidity)
              balance0 balance1)))
        (some (uniswapUint256Value liquidity))) := by
  intro evmL recipient amount0 amount1 totalSupply reserve0 reserve1 nextFrame
    afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOnReturn_of_call
    evm evm0 evm1 evmFee I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOn_kLastNonzero_positiveNoLiquidity evmL evm1
          evmFee I balance0 balance1 feeTo rootK rootKLast
          (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast
          (by simpa [evmL] using hprefix) hroot hrootKNonneg hrootKSize
          hrootKLastNonneg hnumFit hrootFiveFit hdenFit hdenom hfeeLiq)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_kLast evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 true)
    (by simpa [totalSupply] using htotalNonzero)
    (by simpa [evmL, amount0, totalSupply] using hfit0)
    (by simpa [evmL, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by simpa [evmL, amount0, amount1, totalSupply, reserve0, reserve1] using hliquidity)
    hliqNonzero
    (by simpa [totalSupply] using hfitSupply)
    (by simpa [recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [recipient] using helapsed)
    (by simpa [recipient] using hfitKLast)

theorem uniswapMintProportionalFeeOnReturn_kLastNonzeroPositiveWithLiquidity
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress) (rootK rootKLast : Int)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)) feeTo true
          (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt"
            [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
            (uniswapReserve1Word (uniswapLockEnteredState evm)) feeTo true
            (mintFeeKLastWord evmFee) rootK rootKLast)
          evmFee))
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFee rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hfeeLiq : mintFeeLiquidityInt evmFee rootK rootKLast > 0)
    (hfeeLiqFit : (mintFeeLiquidityInt evmFee rootK rootKLast).toNat < UInt256.size)
    (hfeeFitSupply :
      mintFunctionTotalSupplyNewNat evmFee (mintFeeLiquidityWord evmFee rootK rootKLast) <
        UInt256.size)
    (hfeeFitBalance :
      mintFunctionToBalanceNewNat evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast) <
        UInt256.size)
    (htotalNonzero :
      mintFunctionTotalSupplyWord
          (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast)) ≠
        ⟨0⟩)
    (hfit0 :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
          (mintFunctionTotalSupplyWord
            (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))) <
        UInt256.size)
    (hfit1 :
      mintAmountProductNat (mintAmount1Word (uniswapLockEnteredState evm) balance1)
          (mintFunctionTotalSupplyWord
            (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))) <
        UInt256.size)
    (hreserve0Nonzero : uniswapReserve0Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hreserve1Nonzero : uniswapReserve1Word (uniswapLockEnteredState evm) ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord
          (mintProportionalLiquidityWord
            (mintAmount0Word (uniswapLockEnteredState evm) balance0)
            (mintFunctionTotalSupplyWord
              (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast)))
            (uniswapReserve0Word (uniswapLockEnteredState evm)))
          (mintProportionalLiquidityWord
            (mintAmount1Word (uniswapLockEnteredState evm) balance1)
            (mintFunctionTotalSupplyWord
              (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast)))
            (uniswapReserve1Word (uniswapLockEnteredState evm))))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
          liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
        UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
        (mintFunctionPostState
          (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity) = 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1)) < UInt256.size) :
    let feeLiquidity := mintFeeLiquidityWord evmFee rootK rootKLast
    let evmAfterFee := mintFunctionPostState evmFee feeTo feeLiquidity
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let amount0 := mintAmount0Word evmL balance0
    let amount1 := mintAmount1Word evmL balance1
    let totalSupply := mintFunctionTotalSupplyWord evmAfterFee
    let reserve0 := uniswapReserve0Word evmL
    let reserve1 := uniswapReserve1Word evmL
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some (.bool true))
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply" (uniswapUint256Value totalSupply)
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    let afterBranch :=
      resumeAfterInternalCall
        { contract := contract,
          locals :=
            (afterTotalSupplyLocals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some (minFunctionResultValue liquidity0 liquidity1))
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState (mintFunctionPostState evmAfterFee recipient liquidity)
              balance0 balance1)))
        (some (uniswapUint256Value liquidity))) := by
  intro feeLiquidity evmAfterFee evmL recipient amount0 amount1 totalSupply reserve0 reserve1
    nextFrame afterTotalSupplyLocals liquidity0 liquidity1 afterBranch afterMint afterUpdate
  exact uniswapMintAfterMintFeeProportionalFeeOnReturn_of_call
    evm evm0 evm1 evmAfterFee I nextFrame.locals recipient hwv hunlocked hguard0 hguard1
    hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, evmAfterFee, feeLiquidity, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOn_kLastNonzero_positiveWithLiquidity evmL evm1
          evmFee I balance0 balance1 feeTo rootK rootKLast
          (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast
          (by simpa [evmL] using hprefix) hroot hrootKNonneg hrootKSize
          hrootKLastNonneg hnumFit hrootFiveFit hdenFit hdenom hfeeLiq hfeeLiqFit
          hfeeFitSupply hfeeFitBalance)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount0, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, amount1, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_kLast evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 true)
    (by simpa [evmAfterFee, feeLiquidity, totalSupply] using htotalNonzero)
    (by simpa [evmL, evmAfterFee, feeLiquidity, amount0, totalSupply] using hfit0)
    (by simpa [evmL, evmAfterFee, feeLiquidity, amount1, totalSupply] using hfit1)
    (by simpa [evmL, reserve0] using hreserve0Nonzero)
    (by simpa [evmL, reserve1] using hreserve1Nonzero)
    (by
      simpa [evmL, evmAfterFee, feeLiquidity, amount0, amount1, totalSupply, reserve0, reserve1]
        using hliquidity)
    hliqNonzero
    (by simpa [evmAfterFee, feeLiquidity] using hfitSupply)
    (by simpa [evmAfterFee, feeLiquidity, recipient] using hfitBalance)
    hbound0 hbound1
    (by simpa [evmAfterFee, feeLiquidity, recipient] using helapsed)
    (by simpa [evmAfterFee, feeLiquidity, recipient] using hfitKLast)

theorem uniswapMintInitialSmallRootReverts_feeOff_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 : UInt256} (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0)
    (htotalZero : mintFunctionTotalSupplyWord evmFee = ⟨0⟩)
    (hfit :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintAmount1Word (uniswapLockEnteredState evm) balance1) < UInt256.size)
    (hsmall :
      (mintAmountProductWord (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintAmount1Word (uniswapLockEnteredState evm) balance1)).toNat ≤ 3) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  exact uniswapMintAfterMintFeeInitialSmallRootReverts_of_call
    evm evm0 evm1 evmFee I nextFrame.locals hwv hunlocked hguard0 hguard1 hcall0
    hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1 evmFee I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    htotalZero hfit hsmall

theorem uniswapMintInitialSmallRootReverts_feeOn_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 : UInt256} (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0)
    (htotalZero : mintFunctionTotalSupplyWord evmFee = ⟨0⟩)
    (hfit :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintAmount1Word (uniswapLockEnteredState evm) balance1) < UInt256.size)
    (hsmall :
      (mintAmountProductWord (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintAmount1Word (uniswapLockEnteredState evm) balance1)).toNat ≤ 3) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool true))
  exact uniswapMintAfterMintFeeInitialSmallRootReverts_of_call
    evm evm0 evm1 evmFee I nextFrame.locals hwv hunlocked hguard0 hguard1 hcall0
    hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1 evmFee I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 true)
    htotalZero hfit hsmall

theorem uniswapMintInitialSmallRootReverts_feeOff_kLastNonzero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 : UInt256} (feeTo : AccountAddress)
    (hwv : evm.executionEnv.weiValue = ⟨0⟩)
    (hunlocked : Solm.EVM.storageLoad evm evm.executionEnv.codeOwner ⟨12⟩ = ⟨1⟩)
    (hguard0 :
      evalExpr? config
        { contract := contract, locals := mintReserveStore (uniswapLockEnteredState evm) I }
        (uniswapLockEnteredState evm)
        (.binary .gt (.extCodeSize (.storage token0Ref)) (.intLit 0)) = .ok (.bool true))
    (hguard1 :
      evalExpr? config
        { contract := contract,
          locals := (mintReserveStore (uniswapLockEnteredState evm) I).insert "balance0"
            (uniswapUint256Value balance0) } evm0
        (.binary .gt (.extCodeSize (.storage token1Ref)) (.intLit 0)) = .ok (.bool true))
    (hcall0 : typedCallViaEVM config (uniswapLockEnteredState evm)
      (EVM.address (uniswapAddressAtSlot (uniswapLockEnteredState evm) ⟨6⟩))
      "balanceOf" 0 [.address (uniswapLockEnteredState evm).executionEnv.codeOwner]
      (true, evm0, out0) false)
    (hdec0 :
      config.externalABI.decode? "balanceOf" out0 = some (uniswapUint256Value balance0))
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some (uniswapUint256Value balance1))
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfeeGuard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word (uniswapLockEnteredState evm))
          (uniswapReserve1Word (uniswapLockEnteredState evm)))
        evm1 (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hfeeCall : typedCallViaEVM config evm1 (EVM.address (uniswapAddressAtSlot evm1 ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, outFee) false)
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some (.address feeTo))
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (htotalZero : mintFunctionTotalSupplyWord (mintFeeKLastClearedState evmFee) = ⟨0⟩)
    (hfit :
      mintAmountProductNat (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintAmount1Word (uniswapLockEnteredState evm) balance1) < UInt256.size)
    (hsmall :
      (mintAmountProductWord (mintAmount0Word (uniswapLockEnteredState evm) balance0)
        (mintAmount1Word (uniswapLockEnteredState evm) balance1)).toNat ≤ 3) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body .reverted := by
  let evmL := uniswapLockEnteredState evm
  let nextFrame :=
    resumeAfterInternalCall
      { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
      "feeOn" (some (.bool false))
  exact uniswapMintAfterMintFeeInitialSmallRootReverts_of_call
    evm evm0 evm1 (mintFeeKLastClearedState evmFee) I nextFrame.locals hwv hunlocked
    hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastNonzero evmL evm1 evmFee I balance0
          balance1 feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo
          hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, mintAmount0Value] using
      mintAfterMintFeeCallStore_amount0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, mintAmount1Value] using
      mintAfterMintFeeCallStore_amount1 evmL I balance0 balance1 false)
    htotalZero hfit hsmall


end UniswapV2Pair
