import Examples.UniswapV2Pair.MintReturnSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem uniswapMintAfterLiquidityZeroReverts
    {locals : Store} (evm : EVM.State)
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value (⟨0⟩ : UInt256))) :
    ExecBlock config { contract := contract, locals := locals } evm
      mintAfterLiquidityTailStmts .reverted := by
  have hreq :=
    evalExpr_mint_liquidity_gt_zero_false
      (solm := { contract := contract, locals := locals }) evm hliq
  simpa [mintAfterLiquidityTailStmts] using
    (ExecBlock.consRevert (ExecStmt.requireFalse hreq) :
      ExecBlock config { contract := contract, locals := locals } evm
        (.require (.binary .gt (.var "liquidity") (.intLit 0)) ::
          ([ .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
            updateReservesStmtsWith (.var "balance0") (.var "balance1")
              (.var "_reserve0") (.var "_reserve1") ++
            [ .ite (.var "feeOn")
                [ .assign .storage kLastRef
                    (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
                [] ] ++
            lockExit ++
            [ .return [.var "liquidity"] ]))
        .reverted)

theorem uniswapMintProportionalLiquidityZeroReverts
    {locals : Store} (evm : EVM.State)
    (amount0 amount1 totalSupply reserve0 reserve1 : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 totalSupply < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      minFunctionResultWord (mintProportionalLiquidityWord amount0 totalSupply reserve0)
        (mintProportionalLiquidityWord amount1 totalSupply reserve1) = ⟨0⟩) :
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++ mintAfterLiquidityTailStmts) .reverted := by
  let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
  let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
  let afterBranch :=
    resumeAfterInternalCall
      { contract := contract,
        locals :=
          (locals.insert "liquidity0"
            (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
              "liquidity1"
              (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
      "liquidity" (some [minFunctionResultValue liquidity0 liquidity1])
  have hbranchStmt :=
    uniswapMintProportionalLiquidityBranchMin (locals := locals) evm amount0 amount1
      totalSupply reserve0 reserve1 htotal htotalNonzero hamount0 hamount1 hreserve0
      hreserve1 hfit0 hfit1 hreserve0Nonzero hreserve1Nonzero
  have hbranch :
      ExecBlock config { contract := contract, locals := locals } evm [mintLiquidityBranchStmt]
        (.ok afterBranch evm) := by
    exact ExecBlock.consNormal
      (by simpa [liquidity0, liquidity1, afterBranch] using hbranchStmt)
      ExecBlock.nil
  have hliqAfter :
      afterBranch.locals.get? "liquidity" =
        some (uniswapUint256Value (⟨0⟩ : UInt256)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "liquidity" =
            some (uniswapUint256Value (⟨0⟩ : UInt256))
    rw [store_get_self]
    simp [minFunctionResultValue, liquidity0, liquidity1, hliquidity]
  have htail :
      ExecBlock config afterBranch evm mintAfterLiquidityTailStmts .reverted := by
    simpa [afterBranch] using
      uniswapMintAfterLiquidityZeroReverts (locals := afterBranch.locals) evm hliqAfter
  simpa [List.append_assoc] using execBlock_append hbranch htail

theorem evalExpr_mint_initialLiquidity_sub_underflow
    {solm : Frame} (evm : EVM.State) (rootLiquidity : Int)
    (hroot : solm.locals.get? "rootLiquidity" = some (.int rootLiquidity))
    (hlt : rootLiquidity < minimumLiquidity) :
    evalExpr? config solm evm
      (u256 (.binary .sub (.var "rootLiquidity") (.intLit minimumLiquidity))) = .revert := by
  have hneg : rootLiquidity - minimumLiquidity < 0 := by omega
  simp only [u256, evalExpr?, EvalResult.ofOption, hroot, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  change
    (if rootLiquidity - minimumLiquidity < 0 ||
        rootLiquidity - minimumLiquidity ≥ (2 : Int) ^ 256 then
       EvalResult.revert
     else EvalResult.ok (Value.int (rootLiquidity - minimumLiquidity))) =
      EvalResult.revert
  have hcond :
      (decide (rootLiquidity - minimumLiquidity < 0) ||
        decide (rootLiquidity - minimumLiquidity ≥ (2 : Int) ^ 256)) = true := by
    simp only [Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hneg
  rw [if_pos hcond]

theorem uniswapMintInitialLiquiditySmallRootIteReverts
    {locals : Store} (evm : EVM.State) (amount0 amount1 : UInt256)
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value (⟨0⟩ : UInt256)))
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hfit : mintAmountProductNat amount0 amount1 < UInt256.size)
    (hsmall : (mintAmountProductWord amount0 amount1).toNat ≤ 3) :
    ExecStmt config { contract := contract, locals := locals } evm
      mintLiquidityBranchStmt
      .reverted := by
  let y := mintAmountProductWord amount0 amount1
  let caller : Frame := { contract := contract, locals := locals }
  have hcond := evalExpr_mint_totalSupply_eq_zero_true evm htotal
  have hargs :
      evalExprs? config caller evm
        [u256 (.binary .mul (.var "amount0") (.var "amount1"))] =
          .ok [sqrtFunctionYValue y] := by
    simpa [caller, y] using
      evalExprs_mint_initialSqrtArg_of_get evm amount0 amount1 hamount0 hamount1 hfit
  have hsqrt :
      ExecStmt config caller evm
        (.internalCall "sqrt" [u256 (.binary .mul (.var "amount0") (.var "amount1"))]
          "rootLiquidity")
        (.ok (resumeAfterInternalCall caller "rootLiquidity"
          (some [sqrtFunctionSmallResultValue y])) evm) := by
    exact uniswapSqrtFunctionCallSuccess_le3 (caller := caller) (evm := evm) (y := y)
      (args := [u256 (.binary .mul (.var "amount0") (.var "amount1"))])
      (retVar := "rootLiquidity") rfl (by simpa [y] using hsmall) hargs
  refine ExecStmt.iteTrue hcond ?_
  change ExecBlock config caller evm mintInitialLiquidityBranchStmts .reverted
  refine ExecBlock.consNormal hsqrt ?_
  by_cases hy : y.toNat = 0
  · have hroot :
        (resumeAfterInternalCall caller "rootLiquidity"
          (some [sqrtFunctionSmallResultValue y])).locals.get? "rootLiquidity" =
            some (.int 0) := by
      simp [resumeAfterInternalCall, collapseReturns, sqrtFunctionSmallResultValue, hy]
    exact ExecBlock.consRevert
      (ExecStmt.letDeclRevert
        (evalExpr_mint_initialLiquidity_sub_underflow evm 0 hroot
          (by simp [minimumLiquidity])))
  · have hroot :
        (resumeAfterInternalCall caller "rootLiquidity"
          (some [sqrtFunctionSmallResultValue y])).locals.get? "rootLiquidity" =
            some (.int 1) := by
      simp [resumeAfterInternalCall, collapseReturns, sqrtFunctionSmallResultValue, hy]
    exact ExecBlock.consRevert
      (ExecStmt.letDeclRevert
        (evalExpr_mint_initialLiquidity_sub_underflow evm 1 hroot
          (by simp [minimumLiquidity])))

theorem uniswapMintFeeCallFromMint_noCode
    (reserveEvm callEvm : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256)
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool false)) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      .reverted := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_reverts_noCode callEvm reserve0 reserve1 hguard)

theorem uniswapMintFeeCallFromMint_callFailure
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray}
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (false, evmFee, out) false) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      .reverted := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_reverts_callFailure callEvm evmFee reserve0 reserve1
          hguard hcall)

theorem uniswapMintFeeCallFromMint_decodeRevert
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray}
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = none) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      .reverted := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionRevert
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_reverts_decode callEvm evmFee reserve0 reserve1
          hguard hcall hdec)

theorem uniswapMintFeeCallFromMint_feeOff_kLastZero
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray} (feeTo : AccountAddress)
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      (.ok
        (resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
          "feeOn" (some [.bool false]))
        evmFee) := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (calleeEvm := evmFee)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (calleeSolm := mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
    (value := some [.bool false])
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_feeOff_kLastZero callEvm evmFee reserve0 reserve1
          feeTo hguard hcall hdec hfeeTo hkLast)

theorem uniswapMintFeeCallFromMint_feeOn_kLastZero
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray} (feeTo : AccountAddress)
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat = 0) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      (.ok
        (resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
          "feeOn" (some [.bool true]))
        evmFee) := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (calleeEvm := evmFee)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (calleeSolm := mintFeeAfterKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee))
    (value := some [.bool true])
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_feeOn_kLastZero callEvm evmFee reserve0 reserve1
          feeTo hguard hcall hdec hfeeTo hkLast)

theorem uniswapMintFeeCallFromMint_feeOff_kLastNonzero
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray} (feeTo : AccountAddress)
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo = AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      (.ok
        (resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
          "feeOn" (some [.bool false]))
        (mintFeeKLastClearedState evmFee)) := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (calleeEvm := mintFeeKLastClearedState evmFee)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (calleeSolm := mintFeeAfterKLastFrame reserve0 reserve1 feeTo false (mintFeeKLastWord evmFee))
    (value := some [.bool false])
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_feeOff_kLastNonzero callEvm evmFee reserve0 reserve1
          feeTo hguard hcall hdec hfeeTo hkLast)

theorem uniswapMintFeeCallFromMint_feeOn_kLastNonzero_noMint
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray} (feeTo : AccountAddress)
    (rootK rootKLast : Int)
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm)
          feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt"
            [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame (uniswapReserve0Word reserveEvm)
            (uniswapReserve1Word reserveEvm) feeTo true (mintFeeKLastWord evmFee)
            rootK rootKLast)
          evmFee))
    (hroot : ¬ rootK > rootKLast) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      (.ok
        (resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
          "feeOn" (some [.bool true]))
        evmFee) := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (calleeEvm := evmFee)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (calleeSolm :=
      mintFeeAfterRootKLastFrame reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee)
        rootK rootKLast)
    (value := some [.bool true])
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_feeOn_kLastNonzero_noMint callEvm evmFee reserve0
          reserve1 feeTo rootK rootKLast hguard hcall hdec hfeeTo hkLast hprefix hroot)

theorem uniswapMintFeeCallFromMint_feeOn_kLastNonzero_positiveNoLiquidity
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray} (feeTo : AccountAddress)
    (rootK rootKLast : Int)
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm)
          feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt"
            [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame (uniswapReserve0Word reserveEvm)
            (uniswapReserve1Word reserveEvm) feeTo true (mintFeeKLastWord evmFee)
            rootK rootKLast)
          evmFee))
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFee rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : ¬ mintFeeLiquidityInt evmFee rootK rootKLast > 0) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      (.ok
        (resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
          "feeOn" (some [.bool true]))
        evmFee) := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (calleeEvm := evmFee)
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (calleeSolm :=
      mintFeeAfterLiquidityFrame evmFee reserve0 reserve1 feeTo true (mintFeeKLastWord evmFee)
        rootK rootKLast)
    (value := some [.bool true])
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_feeOn_kLastNonzero_positiveNoLiquidity callEvm evmFee
          reserve0 reserve1 feeTo rootK rootKLast hguard hcall hdec hfeeTo hkLast hprefix
          hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit hdenFit
          hdenom hliq)

theorem uniswapMintFeeCallFromMint_feeOn_kLastNonzero_positiveWithLiquidity
    (reserveEvm callEvm evmFee : EVM.State) (I : ExecutionEnv)
    (balance0 balance1 : UInt256) {out : ByteArray} (feeTo : AccountAddress)
    (rootK rootKLast : Int)
    (hguard :
      evalExpr? config
        (mintFeeCallFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm))
        callEvm (.binary .gt (.extCodeSize (.storage factoryRef)) (.intLit 0)) =
          .ok (.bool true))
    (hcall : typedCallViaEVM config callEvm (EVM.address (uniswapAddressAtSlot callEvm ⟨5⟩))
      "feeTo" 0 [] (true, evmFee, out) false)
    (hdec : config.externalABI.decode? "feeTo" out = some [.address feeTo])
    (hfeeTo : feeTo ≠ AccountAddress.ofNat 0)
    (hkLast : (mintFeeKLastWord evmFee).toNat ≠ 0)
    (hprefix :
      ExecBlock config
        (mintFeeAfterKLastFrame (uniswapReserve0Word reserveEvm) (uniswapReserve1Word reserveEvm)
          feeTo true (mintFeeKLastWord evmFee))
        evmFee
        [ .internalCall "sqrt"
            [u256 (.binary .mul (.var "_reserve0") (.var "_reserve1"))] "rootK",
          .internalCall "sqrt" [.var "_kLast"] "rootKLast" ]
        (.ok
          (mintFeeAfterRootKLastFrame (uniswapReserve0Word reserveEvm)
            (uniswapReserve1Word reserveEvm) feeTo true (mintFeeKLastWord evmFee)
            rootK rootKLast)
          evmFee))
    (hroot : rootK > rootKLast) (hrootKNonneg : 0 ≤ rootK)
    (hrootKSize : rootK.toNat < UInt256.size) (hrootKLastNonneg : 0 ≤ rootKLast)
    (hnumFit : mintFeeNumeratorNat evmFee rootK rootKLast < UInt256.size)
    (hrootFiveFit : mintFeeRootTimesFiveNat rootK < UInt256.size)
    (hdenFit : mintFeeDenominatorNat rootK rootKLast < UInt256.size)
    (hdenom : (mintFeeDenominatorWord rootK rootKLast).toNat ≠ 0)
    (hliq : mintFeeLiquidityInt evmFee rootK rootKLast > 0)
    (hliqFit : (mintFeeLiquidityInt evmFee rootK rootKLast).toNat < UInt256.size)
    (hfitSupply :
      mintFunctionTotalSupplyNewNat evmFee (mintFeeLiquidityWord evmFee rootK rootKLast) <
        UInt256.size)
    (hfitBalance :
      mintFunctionToBalanceNewNat evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast) <
        UInt256.size) :
    ExecStmt config
      { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
      callEvm
      (.internalCall "_mintFee" [.var "_reserve0", .var "_reserve1"] "feeOn")
      (.ok
        (resumeAfterInternalCall
          { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 }
          "feeOn" (some [.bool true]))
        (mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))) := by
  let reserve0 := uniswapReserve0Word reserveEvm
  let reserve1 := uniswapReserve1Word reserveEvm
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := mintAmountStore reserveEvm I balance0 balance1 })
    (evm := callEvm)
    (calleeEvm := mintFunctionPostState evmFee feeTo (mintFeeLiquidityWord evmFee rootK rootKLast))
    (name := "_mintFee") (retVar := "feeOn")
    (args := [.var "_reserve0", .var "_reserve1"])
    (argVals := [mintFeeReserve0Value reserve0, mintFeeReserve1Value reserve1])
    (callee := mintFeeFunction)
    (locals := mintFeeCallStore reserve0 reserve1)
    (calleeSolm :=
      mintFeeAfterFeeMintFrame evmFee reserve0 reserve1 feeTo (mintFeeKLastWord evmFee)
        rootK rootKLast)
    (value := some [.bool true])
    (by simpa [reserve0, reserve1] using
      evalExprs_mint_mintFeeArgs reserveEvm callEvm I balance0 balance1)
    (by simpa using uniswapLookupMintFeeFunction)
    (by simpa [reserve0, reserve1] using bindParams_mintFeeFunction_call reserve0 reserve1)
    (by
      simpa [reserve0, reserve1] using
        uniswapMintFeeFunctionBody_feeOn_kLastNonzero_positiveWithLiquidity callEvm evmFee
          reserve0 reserve1 feeTo rootK rootKLast hguard hcall hdec hfeeTo hkLast hprefix
          hroot hrootKNonneg hrootKSize hrootKLastNonneg hnumFit hrootFiveFit hdenFit
          hdenom hliq hliqFit hfitSupply hfitBalance)

end UniswapV2Pair
