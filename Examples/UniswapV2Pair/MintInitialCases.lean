import Examples.UniswapV2Pair.MintInitialSqrtBridge
import Examples.UniswapV2Pair.MintSourcePrefixes
import Examples.UniswapV2Pair.MintRuntimeFinalize
import Examples.UniswapV2Pair.SyncCumulative

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapMintAfterMintFeeInitialRootUnderflowReverts_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 : UInt256}
    (rootLiquidity : Int)
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
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (htotalZero : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (hsqrt :
      ExecStmt config
        { contract := contract,
          locals :=
            nextLocals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
        evmAfter
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextLocals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
            "rootLiquidity" (some [.int rootLiquidity]))
          evmAfter))
    (hlt : rootLiquidity < minimumLiquidity) :
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body .reverted := by
  let afterTotalSupplyLocals :=
    nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee hbase
  have htotal :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value (⟨0⟩ : UInt256)) := by
    simp [afterTotalSupplyLocals, htotalZero]
  have hbranchStmt :
      ExecStmt config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        mintLiquidityBranchStmt .reverted :=
    uniswapMintInitialLiquidityBranchStmtUnderflowReverts evmAfter rootLiquidity htotal
      (by simpa [afterTotalSupplyLocals] using hsqrt) hlt
  have hbranch :
      ExecBlock config { contract := contract, locals := afterTotalSupplyLocals } evmAfter
        [mintLiquidityBranchStmt] .reverted :=
    ExecBlock.consRevert hbranchStmt
  have hthrough := execBlock_append hprefix hbranch
  have hfull :=
    execBlock_append_term (s2 := mintAfterLiquidityTailStmts) hthrough
      (by intro f e h; cases h)
  simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
    mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, List.append_assoc,
    afterTotalSupplyLocals] using hfull

set_option maxHeartbeats 1000000 in
theorem uniswapMintAfterMintFeeInitialFeeOffReturn_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 reserve0 reserve1 liquidity : UInt256}
    (rootLiquidity : Int) (recipient : AccountAddress)
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
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (hto : nextLocals.get? "to" = some (.address recipient))
    (hbalance0 : nextLocals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : nextLocals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : nextLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : nextLocals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hfeeOn : nextLocals.get? "feeOn" = some (.bool false))
    (hreserve0Base : nextLocals.get? "reserve0" = none)
    (hreserve1Base : nextLocals.get? "reserve1" = none)
    (hunlockedBase : nextLocals.get? "unlocked" = none)
    (htotalZero : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (hsqrt :
      ExecStmt config
        { contract := contract,
          locals :=
            nextLocals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
        evmAfter
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextLocals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
            "rootLiquidity" (some [.int rootLiquidity]))
          evmAfter))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMin :
      mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMin :
      mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          recipient liquidity <
        UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
          (mintFunctionPostState
            (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            recipient liquidity) =
        0) :
    let afterTotalSupplyLocals :=
      nextLocals.insert "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
    let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
    let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
    let afterLiquidity : Frame :=
      { contract := contract,
        locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
    let afterMinimum := resumeAfterInternalCall afterLiquidity "_minimumMint" none
    let evmMinimum :=
      mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256)
    let afterMint := resumeAfterInternalCall afterMinimum "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdatePackedReserveState
            (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1))
        (some [uniswapUint256Value liquidity])) := by
  intro afterTotalSupplyLocals caller afterRoot afterLiquidity afterMinimum evmMinimum
    afterMint afterUpdate
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee hbase
  have htotal :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value (⟨0⟩ : UInt256)) := by
    simp [afterTotalSupplyLocals, htotalZero]
  have hto' : afterTotalSupplyLocals.get? "to" = some (.address recipient) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "to" =
        some (.address recipient)
    rw [store_get_ne _ _ (by decide), hto]
  have hbalance0' :
      afterTotalSupplyLocals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "balance0" =
        some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), hbalance0]
  have hbalance1' :
      afterTotalSupplyLocals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "balance1" =
        some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), hbalance1]
  have hreserve0' :
      afterTotalSupplyLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), hreserve0]
  have hreserve1' :
      afterTotalSupplyLocals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), hreserve1]
  have hfeeOn' : afterTotalSupplyLocals.get? "feeOn" = some (.bool false) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "feeOn" =
        some (.bool false)
    rw [store_get_ne _ _ (by decide), hfeeOn]
  have hreserve0Base' : afterTotalSupplyLocals.get? "reserve0" = none := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "reserve0" = none
    rw [store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1Base' : afterTotalSupplyLocals.get? "reserve1" = none := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "reserve1" = none
    rw [store_get_ne _ _ (by decide), hreserve1Base]
  have hunlockedBase' : afterTotalSupplyLocals.get? "unlocked" = none := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "unlocked" = none
    rw [store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config caller evmAfter
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts)
        (.returned afterUpdate
          (uniswapLockExitedState
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1))
          (some [uniswapUint256Value liquidity])) := by
    simpa [caller, afterRoot, afterLiquidity, afterMinimum, evmMinimum, afterMint,
      afterUpdate] using
      uniswapMintInitialLiquidityUpdateElapsedZeroFeeOffReturn
        (locals := afterTotalSupplyLocals) evmAfter rootLiquidity recipient balance0 balance1
        reserve0 reserve1 liquidity htotal hto' hbalance0' hbalance1' hreserve0'
        hreserve1' hfeeOn' hreserve0Base' hreserve1Base' hunlockedBase'
        (by simpa [afterTotalSupplyLocals] using hsqrt) hge hfit hliquidity hliqNonzero
        hfitSupplyMin hfitBalanceMin hfitSupply hfitBalance hbound0 hbound1 helapsed
  have hthrough := execBlock_append hprefix htail
  simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
    mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, List.append_assoc,
    afterTotalSupplyLocals, caller] using hthrough

set_option maxHeartbeats 1000000 in
theorem uniswapMintAfterMintFeeInitialFeeOnReturn_of_call
    (evm evm0 evm1 evmAfter : EVM.State) (I : ExecutionEnv) (nextLocals : Store)
    {out0 out1 : ByteArray} {balance0 balance1 reserve0 reserve1 liquidity : UInt256}
    (rootLiquidity : Int) (recipient : AccountAddress)
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
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
    (henough0 : (uniswapReserve0Word (uniswapLockEnteredState evm)).toNat ≤ balance0.toNat)
    (henough1 : (uniswapReserve1Word (uniswapLockEnteredState evm)).toNat ≤ balance1.toNat)
    (hfee :
      ExecStmt config
        { contract := contract,
          locals := mintAmountStore (uniswapLockEnteredState evm) I balance0 balance1 }
        evm1 (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (hto : nextLocals.get? "to" = some (.address recipient))
    (hbalance0 : nextLocals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : nextLocals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : nextLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : nextLocals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hfeeOn : nextLocals.get? "feeOn" = some (.bool true))
    (hreserve0Base : nextLocals.get? "reserve0" = none)
    (hreserve1Base : nextLocals.get? "reserve1" = none)
    (hkLastBase : nextLocals.get? "kLast" = none)
    (hunlockedBase : nextLocals.get? "unlocked" = none)
    (htotalZero : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (hsqrt :
      ExecStmt config
        { contract := contract,
          locals :=
            nextLocals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
        evmAfter
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextLocals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
            "rootLiquidity" (some [.int rootLiquidity]))
          evmAfter))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMin :
      mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMin :
      mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          recipient liquidity <
        UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
          (mintFunctionPostState
            (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            recipient liquidity) =
        0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
                recipient liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
                recipient liquidity)
              balance0 balance1)) <
        UInt256.size) :
    let afterTotalSupplyLocals :=
      nextLocals.insert "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))
    let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
    let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
    let afterLiquidity : Frame :=
      { contract := contract,
        locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
    let afterMinimum := resumeAfterInternalCall afterLiquidity "_minimumMint" none
    let evmMinimum :=
      mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256)
    let afterMint := resumeAfterInternalCall afterMinimum "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1)))
        (some [uniswapUint256Value liquidity])) := by
  intro afterTotalSupplyLocals caller afterRoot afterLiquidity afterMinimum evmMinimum
    afterMint afterUpdate
  have hprefix :=
    uniswapMintAfterMintFeeTotalSupplyPrefix_of_call evm evm0 evm1 evmAfter I nextLocals
      hwv hunlocked hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee hbase
  have htotal :
      afterTotalSupplyLocals.get? "_totalSupply" =
        some (uniswapUint256Value (⟨0⟩ : UInt256)) := by
    simp [afterTotalSupplyLocals, htotalZero]
  have hto' : afterTotalSupplyLocals.get? "to" = some (.address recipient) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "to" =
        some (.address recipient)
    rw [store_get_ne _ _ (by decide), hto]
  have hbalance0' :
      afterTotalSupplyLocals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "balance0" =
        some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), hbalance0]
  have hbalance1' :
      afterTotalSupplyLocals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "balance1" =
        some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), hbalance1]
  have hreserve0' :
      afterTotalSupplyLocals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_reserve0" =
        some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), hreserve0]
  have hreserve1' :
      afterTotalSupplyLocals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), hreserve1]
  have hfeeOn' : afterTotalSupplyLocals.get? "feeOn" = some (.bool true) := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "feeOn" =
        some (.bool true)
    rw [store_get_ne _ _ (by decide), hfeeOn]
  have hreserve0Base' : afterTotalSupplyLocals.get? "reserve0" = none := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "reserve0" = none
    rw [store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1Base' : afterTotalSupplyLocals.get? "reserve1" = none := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "reserve1" = none
    rw [store_get_ne _ _ (by decide), hreserve1Base]
  have hkLastBase' : afterTotalSupplyLocals.get? "kLast" = none := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "kLast" = none
    rw [store_get_ne _ _ (by decide), hkLastBase]
  have hunlockedBase' : afterTotalSupplyLocals.get? "unlocked" = none := by
    change (nextLocals.insert "_totalSupply"
      (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter))).get? "unlocked" = none
    rw [store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config caller evmAfter
        ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts)
        (.returned afterUpdate
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdatePackedReserveState
                (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1)))
          (some [uniswapUint256Value liquidity])) := by
    simpa [caller, afterRoot, afterLiquidity, afterMinimum, evmMinimum, afterMint,
      afterUpdate] using
      uniswapMintInitialLiquidityUpdateElapsedZeroFeeOnReturn
        (locals := afterTotalSupplyLocals) evmAfter rootLiquidity recipient balance0 balance1
        reserve0 reserve1 liquidity htotal hto' hbalance0' hbalance1' hreserve0'
        hreserve1' hfeeOn' hreserve0Base' hreserve1Base' hkLastBase' hunlockedBase'
        (by simpa [afterTotalSupplyLocals] using hsqrt) hge hfit hliquidity hliqNonzero
        hfitSupplyMin hfitBalanceMin hfitSupply hfitBalance hbound0 hbound1 helapsed
        hfitKLast
  have hthrough := execBlock_append hprefix htail
  simpa [mintTransition, mintLiquidityBranchStmt, mintInitialLiquidityBranchStmts,
    mintProportionalLiquidityBranchStmts, mintAfterLiquidityTailStmts, List.append_assoc,
    afterTotalSupplyLocals, caller] using hthrough

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOffReturn_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress) (rootLiquidity : Int)
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
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0)
    (htotalZero : mintFunctionTotalSupplyWord evmFee = ⟨0⟩)
    (hsqrt :
      let evmL := uniswapLockEnteredState evm
      let nextFrame :=
        resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          "feeOn" (some [.bool false])
      ExecStmt config
        { contract := contract,
          locals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmFee)) }
        evmFee
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextFrame.locals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmFee)) }
            "rootLiquidity" (some [.int rootLiquidity]))
          evmFee))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMin :
      mintFunctionTotalSupplyNewNat evmFee (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMin :
      mintFunctionToBalanceNewNat evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
        UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
          (mintFunctionPostState
            (mintFunctionPostState evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity) =
        0) :
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some [.bool false])
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmFee))
    let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
    let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
    let afterLiquidity : Frame :=
      { contract := contract,
        locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
    let afterMinimum := resumeAfterInternalCall afterLiquidity "_minimumMint" none
    let evmMinimum :=
      mintFunctionPostState evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256)
    let afterMint := resumeAfterInternalCall afterMinimum "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdatePackedReserveState
            (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1))
        (some [uniswapUint256Value liquidity])) := by
  intro evmL recipient nextFrame afterTotalSupplyLocals caller afterRoot afterLiquidity
    afterMinimum evmMinimum afterMint afterUpdate
  exact uniswapMintAfterMintFeeInitialFeeOffReturn_of_call
    evm evm0 evm1 evmFee I nextFrame.locals rootLiquidity recipient hwv hunlocked
    hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOff_kLastZero evmL evm1 evmFee I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 false)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 false)
    htotalZero (by simpa [evmL, nextFrame] using hsqrt) hge hfit hliquidity
    hliqNonzero hfitSupplyMin hfitBalanceMin hfitSupply hfitBalance hbound0 hbound1
    helapsed

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialFeeOnReturn_kLastZero
    (evm evm0 evm1 evmFee : EVM.State) (I : ExecutionEnv)
    {out0 out1 outFee : ByteArray} {balance0 balance1 liquidity : UInt256}
    (feeTo : AccountAddress) (rootLiquidity : Int)
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
      config.externalABI.decode? "balanceOf" out0 = some [uniswapUint256Value balance0])
    (hcall1 : typedCallViaEVM config evm0
      (EVM.address (uniswapAddressAtSlot evm0 ⟨7⟩)) "balanceOf" 0
      [.address evm0.executionEnv.codeOwner] (true, evm1, out1) false)
    (hdec1 :
      config.externalABI.decode? "balanceOf" out1 = some [uniswapUint256Value balance1])
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
    (hfeeDec : config.externalABI.decode? "feeTo" outFee = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0)
    (htotalZero : mintFunctionTotalSupplyWord evmFee = ⟨0⟩)
    (hsqrt :
      let evmL := uniswapLockEnteredState evm
      let nextFrame :=
        resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
          "feeOn" (some [.bool true])
      ExecStmt config
        { contract := contract,
          locals :=
            nextFrame.locals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmFee)) }
        evmFee
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextFrame.locals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmFee)) }
            "rootLiquidity" (some [.int rootLiquidity]))
          evmFee))
    (hge : minimumLiquidity ≤ rootLiquidity)
    (hfit : rootLiquidity - minimumLiquidity < (2 : Int) ^ 256)
    (hliquidity : liquidity = UInt256.ofNat (rootLiquidity - minimumLiquidity).toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupplyMin :
      mintFunctionTotalSupplyNewNat evmFee (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMin :
      mintFunctionToBalanceNewNat evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256) <
        UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          (AccountAddress.ofNat (mintToWord I).toNat) liquidity <
        UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt
          (mintFunctionPostState
            (mintFunctionPostState evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
            (AccountAddress.ofNat (mintToWord I).toNat) liquidity) =
        0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmFee (AccountAddress.ofNat 0)
                  (⟨1000⟩ : UInt256))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmFee (AccountAddress.ofNat 0)
                  (⟨1000⟩ : UInt256))
                (AccountAddress.ofNat (mintToWord I).toNat) liquidity)
              balance0 balance1)) <
        UInt256.size) :
    let evmL := uniswapLockEnteredState evm
    let recipient := AccountAddress.ofNat (mintToWord I).toNat
    let nextFrame :=
      resumeAfterInternalCall
        { contract := contract, locals := mintAmountStore evmL I balance0 balance1 }
        "feeOn" (some [.bool true])
    let afterTotalSupplyLocals :=
      nextFrame.locals.insert "_totalSupply"
        (uniswapUint256Value (mintFunctionTotalSupplyWord evmFee))
    let caller : Frame := { contract := contract, locals := afterTotalSupplyLocals }
    let afterRoot := resumeAfterInternalCall caller "rootLiquidity" (some [.int rootLiquidity])
    let afterLiquidity : Frame :=
      { contract := contract,
        locals := afterRoot.locals.insert "liquidity" (uniswapUint256Value liquidity) }
    let afterMinimum := resumeAfterInternalCall afterLiquidity "_minimumMint" none
    let evmMinimum :=
      mintFunctionPostState evmFee (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256)
    let afterMint := resumeAfterInternalCall afterMinimum "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := mintStore I } evm
      mintTransition.body
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState
              (mintFunctionPostState evmMinimum recipient liquidity) balance0 balance1)))
        (some [uniswapUint256Value liquidity])) := by
  intro evmL recipient nextFrame afterTotalSupplyLocals caller afterRoot afterLiquidity
    afterMinimum evmMinimum afterMint afterUpdate
  exact uniswapMintAfterMintFeeInitialFeeOnReturn_of_call
    evm evm0 evm1 evmFee I nextFrame.locals rootLiquidity recipient hwv hunlocked
    hguard0 hguard1 hcall0 hdec0 hcall1 hdec1 henough0 henough1
    (by
      simpa [nextFrame, evmL, resumeAfterInternalCall] using
        uniswapMintFeeCallFromMint_feeOn_kLastZero evmL evm1 evmFee I balance0 balance1
          feeTo (by simpa [evmL] using hfeeGuard) hfeeCall hfeeDec hfeeTo hkLast)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_totalSupply evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL, recipient, mintToValue] using
      mintAfterMintFeeCallStore_to evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_balance1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1 evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_feeOn evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve0_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_reserve1_base evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_kLast evmL I balance0 balance1 true)
    (by simpa [nextFrame, evmL] using
      mintAfterMintFeeCallStore_unlocked evmL I balance0 balance1 true)
    htotalZero (by simpa [evmL, nextFrame] using hsqrt) hge hfit hliquidity
    hliqNonzero hfitSupplyMin hfitBalanceMin hfitSupply hfitBalance hbound0 hbound1
    helapsed hfitKLast

set_option maxHeartbeats 1000000 in
theorem uniswapMintInitialAfterMintFeeRootUnderflowRevertCase
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evm0S evm1S evmAfter : EVM.State}
    {out0 out1 mem rdata : ByteArray} {k C : ℕ}
    {feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 toWord sel : UInt256}
    (nextLocals : Store) (rootLiquidity : Int)
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
    (henough0 :
      (uniswapReserve0Word
        (uniswapLockEnteredState
          (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I))).toNat ≤
          balance0.toNat)
    (henough1 :
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
                (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)) I balance0
              balance1 }
        evm1S (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
        (.ok { contract := contract, locals := nextLocals } evmAfter))
    (hbase : nextLocals.get? "totalSupply" = none)
    (htotalZero : mintFunctionTotalSupplyWord evmAfter = ⟨0⟩)
    (hsqrt :
      ExecStmt config
        { contract := contract,
          locals :=
            nextLocals.insert "_totalSupply"
              (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
        evmAfter
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok
          (resumeAfterInternalCall
            { contract := contract,
              locals :=
                nextLocals.insert "_totalSupply"
                  (uniswapUint256Value (mintFunctionTotalSupplyWord evmAfter)) }
            "rootLiquidity" (some [.int rootLiquidity]))
          evmAfter))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [UInt256.ofNat rootLiquidity.toNat, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1,
        amount0, balance1, balance0, reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hrootSize : rootLiquidity.toNat < UInt256.size)
    (hrootLt : rootLiquidity < minimumLiquidity)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let evmS := initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I
  have hbody :
      ExecTransitionBody config contract evmS (mintStore I) mintTransition.body .reverted := by
    exact ExecFuncBody.execBlockRevert
      (uniswapMintAfterMintFeeInitialRootUnderflowReverts_of_call evmS evm0S evm1S
        evmAfter I nextLocals rootLiquidity
        (by simp only [evmS, initState]; exact hwv) hunlockedSolm hguard0 hguard1
        hcall0 hdec0 hcall1 hdec1 henough0 henough1 hfee hbase htotalZero hsqrt hrootLt)
  have hrootLtWord :
      (UInt256.ofNat rootLiquidity.toNat).toNat < (⟨1000⟩ : UInt256).toNat := by
    rw [ulit_toNat' _ hrootSize]
    have hrootLtInt : rootLiquidity < (1000 : Int) := by
      simpa [minimumLiquidity] using hrootLt
    have hrootNatLt : rootLiquidity.toNat < 1000 := by
      exact (Int.toNat_lt_of_ne_zero (by decide : (1000 : Nat) ≠ 0)).mpr hrootLtInt
    change rootLiquidity.toNat < 1000
    exact hrootNatLt
  have rdRev :
      RDrev uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) :=
    uniswapMintRuntimeInitialLiquidityAfterRootUnderflowReverts
      (root := UInt256.ofNat rootLiquidity.toNat) rd2531 hrootLtWord hmem hmem64
  exact rdRev.reEquivExecutionRevert hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody

set_option maxHeartbeats 1000000 in
theorem uniswapMintFinishInitialFeeOff
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmAfter : EVM.State}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    {recipient : AccountAddress} {frame : Frame}
    (hcode : I.code = uniswapV2PairBytecode)
    (hdispatch : dispatchMsg contract I.calldata = some mintTransition)
    (hsz36 : 36 ≤ I.calldata.size)
    (hbody :
      ExecTransitionBody config contract
        (initState cA gh bl σ_solm σ₀ (Sat256.ofUInt256 g) A I)
        (mintStore I) mintTransition.body
        (.returned frame
          (uniswapLockExitedState
            (syncUpdatePackedReserveState
              (mintFunctionPostState
                (mintFunctionPostState evmAfter (AccountAddress.ofNat 0)
                  (⟨1000⟩ : UInt256))
                recipient liquidity)
              balance0 balance1))
          (some [uniswapUint256Value liquidity])))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hPostAccountsAfter : accountMapEquiv σFee evmAfter.accountMap)
    (henvAfter : evmAfter.executionEnv = I)
    (hcreatedAfter : evmAfter.createdAccounts = cAFee)
    (hrecipient : recipient = AccountAddress.ofNat toWord.toNat)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hfitSupplySource :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalanceSource :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          recipient liquidity <
        UInt256.size)
    (htotalFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord minimumMem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOff : feeOn = ⟨0⟩)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let minimumMem :=
    uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
      (uniswapInternalMintBalanceHashMem ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
  let σAfterMinimum :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
      (uniswapInternalMintBalanceHashSlot ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
  let evmMinimum :=
    mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256)
  let postMint := mintFunctionPostState evmMinimum recipient liquidity
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord
        (uniswapInternalMintBalanceHashMem toWord minimumMem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
  let packed :=
    uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
  let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
  let syncState := syncUpdatePackedReserveState postMint balance0 balance1
  have hMinimumAccounts : accountMapEquiv σAfterMinimum evmMinimum.accountMap := by
    simpa [evmMinimum, σAfterMinimum] using
      accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient
        (σ := σFee) (evm := evmAfter) (I := I) (mem := mem)
        (recipientWord := ⟨0⟩) (recipient := AccountAddress.ofNat 0)
        hPostAccountsAfter henvAfter rfl (by rw [hmem]; omega)
        hfitSupplyMinSource hfitBalanceMinSource
  have henvMinimum : evmMinimum.executionEnv = I := by
    simp [evmMinimum, mintFunctionPostState, mintFunctionAfterTotalSupplyState, henvAfter,
      storageStore_executionEnv]
  have hminimumMemSize : minimumMem.size = 164 := by
    simpa [minimumMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega)
  have hMintAccounts : accountMapEquiv σAfterMint postMint.accountMap := by
    simpa [postMint, σAfterMint] using
      accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient
        (σ := σAfterMinimum) (evm := evmMinimum) (I := I) (mem := minimumMem)
        (recipientWord := toWord) (recipient := recipient)
        hMinimumAccounts henvMinimum hrecipient (by rw [hminimumMemSize]; omega)
        hfitSupplySource hfitBalanceSource
  have henvMint : postMint.executionEnv = I := by
    simp [postMint, evmMinimum, mintFunctionPostState, mintFunctionAfterTotalSupplyState,
      henvAfter, storageStore_executionEnv]
  have hslot8 :
      Solm.EVM.storageLoad postMint postMint.executionEnv.codeOwner ⟨8⟩ =
        uniswapSlotWord ⟨8⟩ σAfterMint I := by
    have hword := accountMapEquiv_storage_findD hMintAccounts I.codeOwner ⟨8⟩ ⟨0⟩
    simpa [postMint, uniswapSlotWord, Solm.EVM.storageLoad, State.lookupAccount,
      Account.lookupStorage, henvMint] using hword.symm
  have hPackedAccounts : accountMapEquiv σPacked syncState.accountMap := by
    exact accountMapEquiv_syncUpdatePackedReserveState hMintAccounts henvMint hslot8 rfl
  have hAccountsRet :
      accountMapEquiv
        (sstoreAccountMap I.codeOwner σPacked ⟨12⟩ (⟨1⟩ : UInt256))
        (uniswapLockExitedState syncState).accountMap := by
    have hs := accountMapEquiv_sstoreAccountMap I.codeOwner ⟨12⟩ ⟨1⟩ hPackedAccounts
    simpa [uniswapLockExitedState, uniswapUnlockedState, storageStore_accountMap,
      storageStore_executionEnv, syncState, postMint, syncUpdatePackedReserveState,
      henvMint] using hs
  have hCreatedRet : cAFee = (uniswapLockExitedState syncState).createdAccounts := by
    simp [uniswapLockExitedState, uniswapUnlockedState, syncState, postMint, evmMinimum,
      syncUpdatePackedReserveState, mintFunctionPostState, mintFunctionAfterTotalSupplyState,
      storageStore_createdAccounts, hcreatedAfter]
  have rdRet :
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee, sstoreAccountMap I.codeOwner σPacked ⟨12⟩ (⟨1⟩ : UInt256))
        (UInt256.toByteArray liquidity) := by
    simpa [minimumMem, σAfterMinimum, σAfterMint, packed, σPacked] using
      uniswapMintRuntimeInitialLiquidityAfterRootUpdateElapsedZeroFeeOffReturns
        (liquidity := liquidity) rd2531 hliquidity hrootGeMin hliqNonzero hperm
        htotalFitMin hbalanceFitMin htotalFit hbalanceFit hfit0 hfit1 helapsed0 hfeeOff
        hmem hmem64
  exact rdRet.reEquivExecutionGenAccountMapEquiv
    hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody hCreatedRet hAccountsRet
    (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding liquidity))

set_option maxHeartbeats 1000000 in
theorem uniswapMintFinishInitialFeeOn
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256}
    {cAFee : Batteries.RBSet AccountAddress compare} {σFee : AccountMap}
    {evmAfter : EVM.State}
    {mem rdata : ByteArray} {k C : ℕ}
    {root feeOn amount0 amount1 balance0 balance1 reserve0 reserve1 liquidity toWord sel :
      UInt256}
    {recipient : AccountAddress} {frame : Frame}
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
                (mintFunctionPostState
                  (mintFunctionPostState evmAfter (AccountAddress.ofNat 0)
                    (⟨1000⟩ : UInt256))
                  recipient liquidity)
                balance0 balance1)))
          (some [uniswapUint256Value liquidity])))
    (rd2531 : RD uniswapV2PairBytecode I (Sat256.ofUInt256 g)
      (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I) ⟨2531⟩
      [root, ⟨1000⟩, ⟨3742⟩, ⟨0⟩, feeOn, amount1, amount0, balance1, balance0,
        reserve1, reserve0, ⟨0⟩, toWord, ⟨861⟩, sel]
      mem feeToStaticcallActiveWords rdata (cAFee, σFee) k C)
    (hPostAccountsAfter : accountMapEquiv σFee evmAfter.accountMap)
    (henvAfter : evmAfter.executionEnv = I)
    (hcreatedAfter : evmAfter.createdAccounts = cAFee)
    (hrecipient : recipient = AccountAddress.ofNat toWord.toNat)
    (hliquidity : liquidity = UInt256.sub root ⟨1000⟩)
    (hrootGeMin : (⟨1000⟩ : UInt256).toNat ≤ root.toNat)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hperm : I.perm = true)
    (hfitSupplyMinSource :
      mintFunctionTotalSupplyNewNat evmAfter (⟨1000⟩ : UInt256) < UInt256.size)
    (hfitBalanceMinSource :
      mintFunctionToBalanceNewNat evmAfter (AccountAddress.ofNat 0)
          (⟨1000⟩ : UInt256) <
        UInt256.size)
    (htotalFitMin :
      (uniswapSlotWord ⟨0⟩ σFee I).toNat + (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hbalanceFitMin :
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem)).toNat +
          (⟨1000⟩ : UInt256).toNat < UInt256.size)
    (hfitSupplySource :
      mintFunctionTotalSupplyNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          liquidity <
        UInt256.size)
    (hfitBalanceSource :
      mintFunctionToBalanceNewNat
          (mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256))
          recipient liquidity <
        UInt256.size)
    (htotalFit :
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapSlotWord ⟨0⟩ σAfterMinimum I).toNat + liquidity.toNat < UInt256.size)
    (hbalanceFit :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord minimumMem)).toNat + liquidity.toNat <
          UInt256.size)
    (hfit0 : balance0.toNat ≤ reserve112Mask.toNat)
    (hfit1 : balance1.toNat ≤ reserve112Mask.toNat)
    (helapsed0 :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      UInt256.land (uniswapUpdateElapsedWord (uniswapSlotWord ⟨8⟩ σAfterMint I) I)
        reserve32Mask = ⟨0⟩)
    (hfeeOn : feeOn ≠ ⟨0⟩)
    (hfitKLast :
      let minimumMem :=
        uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
          (uniswapInternalMintBalanceHashMem ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      let σAfterMinimum :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σFee ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
          (uniswapInternalMintBalanceHashSlot ⟨0⟩
            (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σFee ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
            (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
      let σAfterMint :=
        sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
            (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
          (uniswapInternalMintBalanceHashSlot toWord
            (uniswapInternalMintBalanceHashMem toWord minimumMem))
          (uniswapCodeOwnerStorageWord I
            (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
              (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
            (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
      let packed := uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
        (uniswapUpdateTimestampWord I) balance1 balance0
      let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
      (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask).toNat *
          (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
            reserve112Mask).toNat < UInt256.size)
    (hmem : mem.size = 164)
    (hmem64 : mem.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩) :
    runtimeEquivalenceFor config contract cA gh bl σ_evm σ_solm σ₀ g A I := by
  let minimumMem :=
    uniswapInternalMintLogMem (⟨1000⟩ : UInt256)
      (uniswapInternalMintBalanceHashMem ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
  let σAfterMinimum :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σFee ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
      (uniswapInternalMintBalanceHashSlot ⟨0⟩
        (uniswapInternalMintBalanceHashMem ⟨0⟩ mem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σFee ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σFee I + (⟨1000⟩ : UInt256)))
        (uniswapInternalMintBalanceHashSlot ⟨0⟩ mem) + (⟨1000⟩ : UInt256))
  let evmMinimum :=
    mintFunctionPostState evmAfter (AccountAddress.ofNat 0) (⟨1000⟩ : UInt256)
  let postMint := mintFunctionPostState evmMinimum recipient liquidity
  let σAfterMint :=
    sstoreAccountMap I.codeOwner
      (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
        (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
      (uniswapInternalMintBalanceHashSlot toWord
        (uniswapInternalMintBalanceHashMem toWord minimumMem))
      (uniswapCodeOwnerStorageWord I
        (sstoreAccountMap I.codeOwner σAfterMinimum ⟨0⟩
          (uniswapSlotWord ⟨0⟩ σAfterMinimum I + liquidity))
        (uniswapInternalMintBalanceHashSlot toWord minimumMem) + liquidity)
  let packed :=
    uniswapUpdatePackedReserveWord (uniswapSlotWord ⟨8⟩ σAfterMint I)
      (uniswapUpdateTimestampWord I) balance1 balance0
  let σPacked := sstoreAccountMap I.codeOwner σAfterMint ⟨8⟩ packed
  let syncState := syncUpdatePackedReserveState postMint balance0 balance1
  let kLastWord :=
    UInt256.mul (UInt256.land (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Mask)
      (UInt256.land (UInt256.div (uniswapSlotWord ⟨8⟩ σPacked I) reserve112Shift)
        reserve112Mask)
  have hMinimumAccounts : accountMapEquiv σAfterMinimum evmMinimum.accountMap := by
    simpa [evmMinimum, σAfterMinimum] using
      accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient
        (σ := σFee) (evm := evmAfter) (I := I) (mem := mem)
        (recipientWord := ⟨0⟩) (recipient := AccountAddress.ofNat 0)
        hPostAccountsAfter henvAfter rfl (by rw [hmem]; omega)
        hfitSupplyMinSource hfitBalanceMinSource
  have henvMinimum : evmMinimum.executionEnv = I := by
    simp [evmMinimum, mintFunctionPostState, mintFunctionAfterTotalSupplyState, henvAfter,
      storageStore_executionEnv]
  have hminimumMemSize : minimumMem.size = 164 := by
    simpa [minimumMem, hmem] using
      uniswapInternalMintSuccessMem_size_of_ge160 ⟨0⟩ (⟨1000⟩ : UInt256)
        (mem := mem) (by rw [hmem]; omega)
  have hMintAccounts : accountMapEquiv σAfterMint postMint.accountMap := by
    simpa [postMint, σAfterMint] using
      accountMapEquiv_mintFunctionPostState_of_runtimeMintRecipient
        (σ := σAfterMinimum) (evm := evmMinimum) (I := I) (mem := minimumMem)
        (recipientWord := toWord) (recipient := recipient)
        hMinimumAccounts henvMinimum hrecipient (by rw [hminimumMemSize]; omega)
        hfitSupplySource hfitBalanceSource
  have henvMint : postMint.executionEnv = I := by
    simp [postMint, evmMinimum, mintFunctionPostState, mintFunctionAfterTotalSupplyState,
      henvAfter, storageStore_executionEnv]
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
      postMint, evmMinimum, syncUpdatePackedReserveState, mintFunctionPostState,
      mintFunctionAfterTotalSupplyState, storageStore_createdAccounts, hcreatedAfter]
  have rdRet :
      RDret uniswapV2PairBytecode (Sat256.ofUInt256 g)
        (initState cA gh bl σ_evm σ₀ (Sat256.ofUInt256 g) A I)
        (cAFee, sstoreAccountMap I.codeOwner
          (sstoreAccountMap I.codeOwner σPacked ⟨11⟩ kLastWord) ⟨12⟩ (⟨1⟩ : UInt256))
        (UInt256.toByteArray liquidity) := by
    simpa [minimumMem, σAfterMinimum, σAfterMint, packed, σPacked, kLastWord] using
      uniswapMintRuntimeInitialLiquidityAfterRootUpdateElapsedZeroFeeOnReturns
        (liquidity := liquidity) rd2531 hliquidity hrootGeMin hliqNonzero hperm
        htotalFitMin hbalanceFitMin htotalFit hbalanceFit hfit0 hfit1 helapsed0
        hfeeOn hfitKLast hmem hmem64
  exact rdRet.reEquivExecutionGenAccountMapEquiv
    hcode hdispatch (uniswapDecode_mint_ok hsz36) hbody hCreatedRet hAccountsRet
    (returnEquiv_of_encode (by simpa [uint256] using uint256ReturnEncoding liquidity))

end UniswapV2Pair
