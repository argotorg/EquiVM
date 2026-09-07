import Examples.UniswapV2Pair.MintCommon
import Examples.UniswapV2Pair.SyncBody

open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

theorem intOfNat_toNat_ne_zero_of_u256_ne_zero (w : UInt256) (h : w ≠ ⟨0⟩) :
    Int.ofNat w.toNat ≠ 0 := by
  intro hzero
  apply h
  apply u256_inj
  have hnat : w.toNat = 0 := by
    exact Int.ofNat_eq_zero.mp hzero
  simpa using hnat

theorem uniswapMintProportionalLiquidityBranchMin
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
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩) :
    let liquidity0 := mintProportionalLiquidityWord amount0 totalSupply reserve0
    let liquidity1 := mintProportionalLiquidityWord amount1 totalSupply reserve1
    ExecStmt config { contract := contract, locals := locals } evm
      mintLiquidityBranchStmt
      (.ok
        (resumeAfterInternalCall
          { contract := contract,
            locals :=
              (locals.insert "liquidity0"
                (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                  "liquidity1"
                  (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
          "liquidity" (some [minFunctionResultValue liquidity0 liquidity1]))
        evm) := by
  intro liquidity0 liquidity1
  have hcond := evalExpr_mint_totalSupply_eq_zero_false evm totalSupply htotal htotalNonzero
  have hliq0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.binary .div
          (u256 (.binary .mul (.var "amount0") (.var "_totalSupply")))
          (.var "_reserve0")) =
          .ok (mintProportionalLiquidityValue amount0 totalSupply reserve0) :=
    evalExpr_mint_proportionalLiquidity_of_get evm "amount0" "_reserve0" amount0
      totalSupply reserve0 hamount0 htotal hreserve0 hfit0 hreserve0Nonzero
  let locals0 :=
    locals.insert "liquidity0" (mintProportionalLiquidityValue amount0 totalSupply reserve0)
  have hamount1' :
      locals0.get? "amount1" = some (uniswapUint256Value amount1) := by
    change (locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).get? "amount1" =
        some (uniswapUint256Value amount1)
    rw [store_get_ne _ _ (by decide), hamount1]
  have htotal' :
      locals0.get? "_totalSupply" = some (uniswapUint256Value totalSupply) := by
    change (locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).get? "_totalSupply" =
        some (uniswapUint256Value totalSupply)
    rw [store_get_ne _ _ (by decide), htotal]
  have hreserve1' :
      locals0.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).get? "_reserve1" =
        some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), hreserve1]
  have hliq1 :
      evalExpr? config { contract := contract, locals := locals0 } evm
        (.binary .div
          (u256 (.binary .mul (.var "amount1") (.var "_totalSupply")))
          (.var "_reserve1")) =
          .ok (mintProportionalLiquidityValue amount1 totalSupply reserve1) :=
    evalExpr_mint_proportionalLiquidity_of_get evm "amount1" "_reserve1" amount1
      totalSupply reserve1 hamount1' htotal' hreserve1' hfit1 hreserve1Nonzero
  let locals1 :=
    locals0.insert "liquidity1" (mintProportionalLiquidityValue amount1 totalSupply reserve1)
  have hminArgs :
      evalExprs? config { contract := contract, locals := locals1 } evm
        [.var "liquidity0", .var "liquidity1"] =
          .ok [minFunctionXValue liquidity0, minFunctionYValue liquidity1] := by
    have hliq0Lookup : locals1.get? "liquidity0" =
        some (mintProportionalLiquidityValue amount0 totalSupply reserve0) := by
      change ((locals.insert "liquidity0"
        (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
          (mintProportionalLiquidityValue amount1 totalSupply reserve1)).get? "liquidity0" =
            some (mintProportionalLiquidityValue amount0 totalSupply reserve0)
      rw [store_get_ne _ _ (by decide), store_get_self]
    have hliq1Lookup : locals1.get? "liquidity1" =
        some (mintProportionalLiquidityValue amount1 totalSupply reserve1) := by
      change ((locals.insert "liquidity0"
        (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
          (mintProportionalLiquidityValue amount1 totalSupply reserve1)).get? "liquidity1" =
            some (mintProportionalLiquidityValue amount1 totalSupply reserve1)
      rw [store_get_self]
    simp only [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure]
    rw [hliq0Lookup, hliq1Lookup]
  change ExecStmt config { contract := contract, locals := locals } evm
    (.ite (.binary .eq (.var "_totalSupply") (.intLit 0))
      mintInitialLiquidityBranchStmts mintProportionalLiquidityBranchStmts)
    (.ok
      (resumeAfterInternalCall
        { contract := contract,
          locals :=
            (locals.insert "liquidity0"
              (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert
                "liquidity1"
                (mintProportionalLiquidityValue amount1 totalSupply reserve1) }
        "liquidity" (some [minFunctionResultValue liquidity0 liquidity1])) evm)
  refine ExecStmt.iteFalse hcond ?_
  change ExecBlock config { contract := contract, locals := locals } evm
    mintProportionalLiquidityBranchStmts
    (.ok
      (resumeAfterInternalCall { contract := contract, locals := locals1 } "liquidity"
        (some [minFunctionResultValue liquidity0 liquidity1])) evm)
  refine ExecBlock.consNormal (ExecStmt.letDecl hliq0) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl hliq1) ?_
  exact ExecBlock.consNormal
    (uniswapMinFunctionCallSuccess (caller := { contract := contract, locals := locals1 })
      (evm := evm) (x := liquidity0) (y := liquidity1)
      (args := [.var "liquidity0", .var "liquidity1"]) (retVar := "liquidity")
      rfl hminArgs)
    ExecBlock.nil

theorem evalExpr_mint_liquidity_gt_zero_true
    {solm : Frame} (evm : EVM.State) (liquidity : UInt256)
    (hliq : solm.locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hzero : liquidity ≠ ⟨0⟩) :
    evalExpr? config solm evm (.binary .gt (.var "liquidity") (.intLit 0)) =
      .ok (.bool true) := by
  have hnat : 0 < liquidity.toNat := by
    by_contra h
    have hz : liquidity.toNat = 0 := by omega
    exact hzero (uint256_toNat_eq_zero hz)
  simp only [evalExpr?, EvalResult.ofOption, hliq, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?, hnat]

theorem evalExpr_mint_liquidity_gt_zero_false
    {solm : Frame} (evm : EVM.State)
    (hliq : solm.locals.get? "liquidity" = some (uniswapUint256Value (⟨0⟩ : UInt256))) :
    evalExpr? config solm evm (.binary .gt (.var "liquidity") (.intLit 0)) =
      .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, hliq, EvalResult.bind, bind, pure]
  simp [evalBinaryOp?]

theorem evalExprs_mint_finalMintArgs_of_get
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress) (liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (mintFunctionValueValue liquidity)) :
    evalExprs? config { contract := contract, locals := locals } evm
      [.var "to", .var "liquidity"] =
        .ok [mintFunctionToValue recipient, mintFunctionValueValue liquidity] := by
  simp only [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    mintFunctionToValue]
  rw [hto, hliq]

theorem uniswapMintLiquidityMintPrefix
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress) (liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size) :
    ExecBlock config { contract := contract, locals := locals } evm
      [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
        .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ]
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          "_mintResult" none)
        (mintFunctionPostState evm recipient liquidity)) := by
  have hreq := evalExpr_mint_liquidity_gt_zero_true
    (solm := { contract := contract, locals := locals }) evm liquidity (by simpa using hliq)
    hliqNonzero
  have hargs :
      evalExprs? config { contract := contract, locals := locals } evm
        [.var "to", .var "liquidity"] =
          .ok [mintFunctionToValue recipient, mintFunctionValueValue liquidity] := by
    exact evalExprs_mint_finalMintArgs_of_get evm recipient liquidity hto
      (by simpa [mintFunctionValueValue] using hliq)
  refine ExecBlock.consNormal (ExecStmt.requireTrue hreq) ?_
  exact ExecBlock.consNormal
    (uniswapMintFunctionCallSuccess
      (caller := { contract := contract, locals := locals }) (evm := evm)
      (recipient := recipient) (value := liquidity)
      (args := [.var "to", .var "liquidity"]) (retVar := "_mintResult")
      rfl hargs hfitSupply hfitBalance)
    ExecBlock.nil

theorem uniswapMintProportionalLiquidityMintPrefix
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
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
      liquidity =
        minFunctionResultWord (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size) :
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
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ])
      (.ok (resumeAfterInternalCall afterBranch "_mintResult" none)
        (mintFunctionPostState evm recipient liquidity)) := by
  intro liquidity0 liquidity1 afterBranch
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
  have htoAfter :
      afterBranch.locals.get? "to" = some (.address recipient) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "to" =
            some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hto]
  have hliqAfter :
      afterBranch.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "liquidity" =
            some (uniswapUint256Value liquidity)
    rw [store_get_self]
    simp [minFunctionResultValue, liquidity0, liquidity1, hliquidity]
  have hmint :
      ExecBlock config afterBranch evm
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ]
        (.ok (resumeAfterInternalCall afterBranch "_mintResult" none)
          (mintFunctionPostState evm recipient liquidity)) := by
    simpa [afterBranch] using
      uniswapMintLiquidityMintPrefix (locals := afterBranch.locals) evm recipient liquidity
        htoAfter hliqAfter hliqNonzero hfitSupply hfitBalance
  simpa [List.append_assoc] using execBlock_append hbranch hmint

theorem evalExprs_mint_updateCallArgs_of_get
    {locals : Store} (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none) :
    evalExprs? config { contract := contract, locals := locals } evm
      [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ] =
        .ok (syncUpdateCallArgVals evm balance0 balance1) := by
  have h0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "balance0") = .ok (uniswapUint256Value balance0) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hbalance0]
  have h1 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "balance1") = .ok (uniswapUint256Value balance1) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hbalance1]
  have hr0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage reserve0Ref) = .ok (.int (Int.ofNat (uniswapReserve0Word evm).toNat)) :=
    evalExpr_uniswap_reserve0 evm locals hreserve0Base
  have hr1 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.storage reserve1Ref) = .ok (.int (Int.ofNat (uniswapReserve1Word evm).toNat)) :=
    evalExpr_uniswap_reserve1 evm locals hreserve1Base
  simp only [evalExprs?, EvalResult.bind, bind, syncUpdateCallArgVals]
  rw [h0, h1, hr0, hr1]
  rfl

theorem evalExprs_mint_updateCallArgsWith_of_get
    {locals : Store} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 :
      locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat))) :
    evalExprs? config { contract := contract, locals := locals } evm
      [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ] =
        .ok (syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1) := by
  have h0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "balance0") = .ok (uniswapUint256Value balance0) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hbalance0]
  have h1 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "balance1") = .ok (uniswapUint256Value balance1) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hbalance1]
  have hr0 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "_reserve0") =
          .ok (.int (Int.ofNat reserve0.toNat)) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hreserve0]
  have hr1 :
      evalExpr? config { contract := contract, locals := locals } evm
        (.var "_reserve1") =
          .ok (.int (Int.ofNat reserve1.toNat)) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [hreserve1]
  simp only [evalExprs?, EvalResult.bind, bind, syncUpdateCallArgValsWith]
  rw [h0, h1, hr0, hr1]
  rfl

theorem uniswapMintUpdateCallReturns_conditionFalse_packed
    {locals : Store} (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (hcond :
      evalExpr? config
        { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 }
        evm
        (.binary .and
          (.binary .gt (.var "timeElapsed") (.intLit 0))
          (.binary .and
            (.binary .ne (.var "_reserve0") (.intLit 0))
            (.binary .ne (.var "_reserve1") (.intLit 0)))) = .ok (.bool false)) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
        "_updateResult")
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          "_updateResult" none)
        (syncUpdatePackedReserveState evm balance0 balance1)) := by
  have hargs :=
    evalExprs_mint_updateCallArgs_of_get evm balance0 balance1 hbalance0 hbalance1
      hreserve0Base hreserve1Base
  have hbody :=
    uniswapUpdateFunctionReturns_conditionFalse_packed evm balance0 balance1
      hbound0 hbound1 hcond
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := locals })
    (evm := evm)
    (calleeEvm := syncUpdatePackedReserveState evm balance0 balance1)
    (name := "_update") (retVar := "_updateResult")
    (args := [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ])
    (argVals := syncUpdateCallArgVals evm balance0 balance1)
    (callee := updateFunction)
    (locals := syncUpdateCallStore evm balance0 balance1)
    (calleeSolm :=
      { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 })
    (value := none)
    hargs
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call evm balance0 balance1)
    hbody

theorem uniswapMintUpdateCallReturns_elapsedZero_packed
    {locals : Store} (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : syncTimeElapsedInt evm = 0) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
        "_updateResult")
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          "_updateResult" none)
        (syncUpdatePackedReserveState evm balance0 balance1)) := by
  exact uniswapMintUpdateCallReturns_conditionFalse_packed evm balance0 balance1
    hbalance0 hbalance1 hreserve0Base hreserve1Base hbound0 hbound1
    (evalExpr_sync_update_condition_false_elapsed_zero evm balance0 balance1 helapsed)

theorem uniswapMintUpdateCallReverts_firstBound_with
    {locals : Store} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 :
      locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
        "_updateResult") .reverted := by
  exact internalCallFunctionRevert
    (callee := updateFunction)
    (locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1)
    (evalExprs_mint_updateCallArgsWith_of_get evm balance0 balance1 reserve0 reserve1
      hbalance0 hbalance1 hreserve0 hreserve1)
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call_with balance0 balance1 reserve0 reserve1)
    (uniswapUpdateFunctionReverts_firstBound_with evm balance0 balance1 reserve0 reserve1
      hbound)

theorem uniswapMintUpdateCallReverts_secondBound_with
    {locals : Store} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 :
      locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
        "_updateResult") .reverted := by
  exact internalCallFunctionRevert
    (callee := updateFunction)
    (locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1)
    (evalExprs_mint_updateCallArgsWith_of_get evm balance0 balance1 reserve0 reserve1
      hbalance0 hbalance1 hreserve0 hreserve1)
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call_with balance0 balance1 reserve0 reserve1)
    (uniswapUpdateFunctionReverts_secondBound_with evm balance0 balance1 reserve0 reserve1
      hbound0 hbound1)

theorem uniswapMintUpdateCallReturns_elapsedZero_packed_with
    {locals : Store} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 :
      locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : syncTimeElapsedInt evm = 0) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
        "_updateResult")
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          "_updateResult" none)
        (syncUpdatePackedReserveState evm balance0 balance1)) := by
  have hargs :=
    evalExprs_mint_updateCallArgsWith_of_get evm balance0 balance1 reserve0 reserve1
      hbalance0 hbalance1 hreserve0 hreserve1
  have hbody :=
    uniswapUpdateFunctionReturns_conditionFalse_packed_with evm balance0 balance1 reserve0
      reserve1
      hbound0 hbound1
      (evalExpr_sync_update_condition_false_elapsed_zero_with evm balance0 balance1 reserve0
        reserve1 helapsed)
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := locals })
    (evm := evm)
    (calleeEvm := syncUpdatePackedReserveState evm balance0 balance1)
    (name := "_update") (retVar := "_updateResult")
    (args := [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ])
    (argVals := syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1)
    (callee := updateFunction)
    (locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1)
    (calleeSolm :=
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 })
    (value := none)
    hargs
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call_with balance0 balance1 reserve0 reserve1)
    hbody

theorem uniswapMintUpdateCallReturns_conditionTrue_packed
    {locals : Store} (evm : EVM.State) (balance0 balance1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0 : Int.ofNat (uniswapReserve0Word evm).toNat ≠ 0)
    (hreserve1 : Int.ofNat (uniswapReserve1Word evm).toNat ≠ 0) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ]
        "_updateResult")
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          "_updateResult" none)
        (syncUpdateCumulativePackedReserveState evm balance0 balance1)) := by
  have hargs :=
    evalExprs_mint_updateCallArgs_of_get evm balance0 balance1 hbalance0 hbalance1
      hreserve0Base hreserve1Base
  have hbody :=
    uniswapUpdateFunctionReturns_conditionTrue_packed evm balance0 balance1
      hbound0 hbound1 helapsed hreserve0 hreserve1
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := locals })
    (evm := evm)
    (calleeEvm := syncUpdateCumulativePackedReserveState evm balance0 balance1)
    (name := "_update") (retVar := "_updateResult")
    (args := [ .var "balance0", .var "balance1", .storage reserve0Ref, .storage reserve1Ref ])
    (argVals := syncUpdateCallArgVals evm balance0 balance1)
    (callee := updateFunction)
    (locals := syncUpdateCallStore evm balance0 balance1)
    (calleeSolm :=
      { contract := contract, locals := syncUpdateTimeElapsedStore evm balance0 balance1 })
    (value := none)
    hargs
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call evm balance0 balance1)
    hbody

theorem uniswapMintUpdateCallReturns_conditionTrue_packed_with
    {locals : Store} (evm : EVM.State) (balance0 balance1 reserve0 reserve1 : UInt256)
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 :
      locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed : 0 < syncTimeElapsedInt evm)
    (hreserve0Ne : Int.ofNat reserve0.toNat ≠ 0)
    (hreserve1Ne : Int.ofNat reserve1.toNat ≠ 0) :
    ExecStmt config { contract := contract, locals := locals } evm
      (.internalCall "_update"
        [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
        "_updateResult")
      (.ok
        (resumeAfterInternalCall { contract := contract, locals := locals }
          "_updateResult" none)
        (syncUpdateCumulativePackedReserveStateWith evm balance0 balance1 reserve0 reserve1)) := by
  have hargs :=
    evalExprs_mint_updateCallArgsWith_of_get evm balance0 balance1 reserve0 reserve1
      hbalance0 hbalance1 hreserve0 hreserve1
  have hbody :=
    uniswapUpdateFunctionReturns_conditionTrue_packed_with evm balance0 balance1 reserve0
      reserve1 hbound0 hbound1 helapsed hreserve0Ne hreserve1Ne
  exact internalCallFunctionReturn
    (cfg := config)
    (caller := { contract := contract, locals := locals })
    (evm := evm)
    (calleeEvm := syncUpdateCumulativePackedReserveStateWith evm balance0 balance1 reserve0
      reserve1)
    (name := "_update") (retVar := "_updateResult")
    (args := [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ])
    (argVals := syncUpdateCallArgValsWith balance0 balance1 reserve0 reserve1)
    (callee := updateFunction)
    (locals := syncUpdateCallStoreWith balance0 balance1 reserve0 reserve1)
    (calleeSolm :=
      { contract := contract,
        locals := syncUpdateTimeElapsedStoreWith evm balance0 balance1 reserve0 reserve1 })
    (value := none)
    hargs
    uniswapLookupUpdateFunction
    (bindParams_sync_update_call_with balance0 balance1 reserve0 reserve1)
    hbody

theorem uniswapMintLiquidityMintUpdateElapsedZeroPrefix
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (balance0 balance1 reserve0 reserve1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 :
      locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt (mintFunctionPostState evm recipient liquidity) = 0) :
    let afterMint :=
      resumeAfterInternalCall { contract := contract, locals := locals } "_mintResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
        .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
      (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
        (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
          balance0 balance1)) := by
  intro afterMint
  have hmint :=
    uniswapMintLiquidityMintPrefix (locals := locals) evm recipient liquidity hto hliq
      hliqNonzero hfitSupply hfitBalance
  have hbalance0After :
      afterMint.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (locals.insert "_mintResult" Value.unit).get? "balance0" =
      some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), hbalance0]
  have hbalance1After :
      afterMint.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (locals.insert "_mintResult" Value.unit).get? "balance1" =
      some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), hbalance1]
  have hreserve0After :
      afterMint.locals.get? "reserve0" = none := by
    change (locals.insert "_mintResult" Value.unit).get? "reserve0" = none
    rw [store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1After :
      afterMint.locals.get? "reserve1" = none := by
    change (locals.insert "_mintResult" Value.unit).get? "reserve1" = none
    rw [store_get_ne _ _ (by decide), hreserve1Base]
  have hreserve0ArgAfter :
      afterMint.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (locals.insert "_mintResult" Value.unit).get? "_reserve0" =
      some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), hreserve0]
  have hreserve1ArgAfter :
      afterMint.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (locals.insert "_mintResult" Value.unit).get? "_reserve1" =
      some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), hreserve1]
  have hupdateStmt :
      ExecStmt config afterMint (mintFunctionPostState evm recipient liquidity)
        (.internalCall "_update"
          [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
          "_updateResult")
        (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
          (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
            balance0 balance1)) := by
    simpa [afterMint] using
      uniswapMintUpdateCallReturns_elapsedZero_packed_with
        (locals := afterMint.locals)
        (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1
        hbalance0After hbalance1After hreserve0ArgAfter hreserve1ArgAfter hbound0 hbound1
        helapsed
  have hupdate :
      ExecBlock config afterMint (mintFunctionPostState evm recipient liquidity)
        (updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
        (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
          (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
            balance0 balance1)) := by
    simpa [updateReservesStmtsWith] using ExecBlock.consNormal hupdateStmt ExecBlock.nil
  simpa [List.append_assoc] using execBlock_append hmint hupdate

theorem uniswapMintLiquidityMintUpdateCumulativePrefix
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (balance0 balance1 reserve0 reserve1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 :
      locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 :
      locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      0 < syncTimeElapsedInt (mintFunctionPostState evm recipient liquidity))
    (hreserve0Ne : Int.ofNat reserve0.toNat ≠ 0)
    (hreserve1Ne : Int.ofNat reserve1.toNat ≠ 0) :
    let afterMint :=
      resumeAfterInternalCall { contract := contract, locals := locals } "_mintResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
        .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
      (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
        (syncUpdateCumulativePackedReserveStateWith
          (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1)) := by
  intro afterMint
  have hmint :=
    uniswapMintLiquidityMintPrefix (locals := locals) evm recipient liquidity hto hliq
      hliqNonzero hfitSupply hfitBalance
  have hbalance0After :
      afterMint.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (locals.insert "_mintResult" Value.unit).get? "balance0" =
      some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), hbalance0]
  have hbalance1After :
      afterMint.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (locals.insert "_mintResult" Value.unit).get? "balance1" =
      some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), hbalance1]
  have hreserve0After :
      afterMint.locals.get? "reserve0" = none := by
    change (locals.insert "_mintResult" Value.unit).get? "reserve0" = none
    rw [store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1After :
      afterMint.locals.get? "reserve1" = none := by
    change (locals.insert "_mintResult" Value.unit).get? "reserve1" = none
    rw [store_get_ne _ _ (by decide), hreserve1Base]
  have hreserve0ArgAfter :
      afterMint.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (locals.insert "_mintResult" Value.unit).get? "_reserve0" =
      some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), hreserve0]
  have hreserve1ArgAfter :
      afterMint.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (locals.insert "_mintResult" Value.unit).get? "_reserve1" =
      some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), hreserve1]
  have hupdateStmt :
      ExecStmt config afterMint (mintFunctionPostState evm recipient liquidity)
        (.internalCall "_update"
          [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
          "_updateResult")
        (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
          (syncUpdateCumulativePackedReserveStateWith
            (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
            reserve1)) := by
    simpa [afterMint] using
      uniswapMintUpdateCallReturns_conditionTrue_packed_with
        (locals := afterMint.locals)
        (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1
        hbalance0After hbalance1After hreserve0ArgAfter hreserve1ArgAfter hbound0 hbound1
        helapsed hreserve0Ne hreserve1Ne
  have hupdate :
      ExecBlock config afterMint (mintFunctionPostState evm recipient liquidity)
        (updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
        (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
          (syncUpdateCumulativePackedReserveStateWith
            (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
            reserve1)) := by
    simpa [updateReservesStmtsWith] using ExecBlock.consNormal hupdateStmt ExecBlock.nil
  simpa [List.append_assoc] using execBlock_append hmint hupdate

theorem uniswapMintProportionalLiquidityUpdateFirstBoundReverts
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 balance0 balance1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 totalSupply < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound : maxUint112 < Int.ofNat balance0.toNat) :
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
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
      .reverted := by
  intro liquidity0 liquidity1 afterBranch
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
  have htoAfter :
      afterBranch.locals.get? "to" = some (.address recipient) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "to" =
            some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hto]
  have hliqAfter :
      afterBranch.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "liquidity" =
            some (uniswapUint256Value liquidity)
    rw [store_get_self]
    simp [minFunctionResultValue, liquidity0, liquidity1, hliquidity]
  have hbalance0After :
      afterBranch.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "balance0" =
            some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance0]
  have hbalance1After :
      afterBranch.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "balance1" =
            some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance1]
  have hreserve0After :
      afterBranch.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "_reserve0" =
            some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0]
  have hreserve1After :
      afterBranch.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "_reserve1" =
            some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1]
  have hmint :=
    uniswapMintLiquidityMintPrefix (locals := afterBranch.locals) evm recipient liquidity
      htoAfter hliqAfter hliqNonzero hfitSupply hfitBalance
  have hupdateStmt :
      ExecStmt config (resumeAfterInternalCall afterBranch "_mintResult" none)
        (mintFunctionPostState evm recipient liquidity)
        (.internalCall "_update"
          [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
          "_updateResult")
        .reverted := by
    simpa [afterBranch] using
      uniswapMintUpdateCallReverts_firstBound_with
        (locals := (resumeAfterInternalCall afterBranch "_mintResult" none).locals)
        (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1
        (by
          change (afterBranch.locals.insert "_mintResult" Value.unit).get? "balance0" =
            some (uniswapUint256Value balance0)
          rw [store_get_ne _ _ (by decide), hbalance0After])
        (by
          change (afterBranch.locals.insert "_mintResult" Value.unit).get? "balance1" =
            some (uniswapUint256Value balance1)
          rw [store_get_ne _ _ (by decide), hbalance1After])
        (by
          change (afterBranch.locals.insert "_mintResult" Value.unit).get? "_reserve0" =
            some (.int (Int.ofNat reserve0.toNat))
          rw [store_get_ne _ _ (by decide), hreserve0After])
        (by
          change (afterBranch.locals.insert "_mintResult" Value.unit).get? "_reserve1" =
            some (.int (Int.ofNat reserve1.toNat))
          rw [store_get_ne _ _ (by decide), hreserve1After])
        hbound
  have hupdate :
      ExecBlock config (resumeAfterInternalCall afterBranch "_mintResult" none)
        (mintFunctionPostState evm recipient liquidity)
        (updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
        .reverted := by
    simpa [updateReservesStmtsWith] using ExecBlock.consRevert hupdateStmt
  have htail := execBlock_append hmint hupdate
  simpa [List.append_assoc] using execBlock_append hbranch htail

theorem uniswapMintProportionalLiquidityUpdateSecondBoundReverts
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 balance0 balance1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 totalSupply < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : maxUint112 < Int.ofNat balance1.toNat) :
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
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
      .reverted := by
  intro liquidity0 liquidity1 afterBranch
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
  have htoAfter :
      afterBranch.locals.get? "to" = some (.address recipient) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "to" =
            some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hto]
  have hliqAfter :
      afterBranch.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "liquidity" =
            some (uniswapUint256Value liquidity)
    rw [store_get_self]
    simp [minFunctionResultValue, liquidity0, liquidity1, hliquidity]
  have hbalance0After :
      afterBranch.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "balance0" =
            some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance0]
  have hbalance1After :
      afterBranch.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "balance1" =
            some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance1]
  have hreserve0After :
      afterBranch.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "_reserve0" =
            some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0]
  have hreserve1After :
      afterBranch.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "_reserve1" =
            some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1]
  have hmint :=
    uniswapMintLiquidityMintPrefix (locals := afterBranch.locals) evm recipient liquidity
      htoAfter hliqAfter hliqNonzero hfitSupply hfitBalance
  have hupdateStmt :
      ExecStmt config (resumeAfterInternalCall afterBranch "_mintResult" none)
        (mintFunctionPostState evm recipient liquidity)
        (.internalCall "_update"
          [ .var "balance0", .var "balance1", .var "_reserve0", .var "_reserve1" ]
          "_updateResult")
        .reverted := by
    simpa [afterBranch] using
      uniswapMintUpdateCallReverts_secondBound_with
        (locals := (resumeAfterInternalCall afterBranch "_mintResult" none).locals)
        (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1
        (by
          change (afterBranch.locals.insert "_mintResult" Value.unit).get? "balance0" =
            some (uniswapUint256Value balance0)
          rw [store_get_ne _ _ (by decide), hbalance0After])
        (by
          change (afterBranch.locals.insert "_mintResult" Value.unit).get? "balance1" =
            some (uniswapUint256Value balance1)
          rw [store_get_ne _ _ (by decide), hbalance1After])
        (by
          change (afterBranch.locals.insert "_mintResult" Value.unit).get? "_reserve0" =
            some (.int (Int.ofNat reserve0.toNat))
          rw [store_get_ne _ _ (by decide), hreserve0After])
        (by
          change (afterBranch.locals.insert "_mintResult" Value.unit).get? "_reserve1" =
            some (.int (Int.ofNat reserve1.toNat))
          rw [store_get_ne _ _ (by decide), hreserve1After])
        hbound0 hbound1
  have hupdate :
      ExecBlock config (resumeAfterInternalCall afterBranch "_mintResult" none)
        (mintFunctionPostState evm recipient liquidity)
        (updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
        .reverted := by
    simpa [updateReservesStmtsWith] using ExecBlock.consRevert hupdateStmt
  have htail := execBlock_append hmint hupdate
  simpa [List.append_assoc] using execBlock_append hbranch htail

theorem uniswapMintProportionalLiquidityUpdateElapsedZeroPrefix
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 balance0 balance1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 totalSupply < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt (mintFunctionPostState evm recipient liquidity) = 0) :
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
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
      (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
        (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
          balance0 balance1)) := by
  intro liquidity0 liquidity1 afterBranch afterMint
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
  have htoAfter :
      afterBranch.locals.get? "to" = some (.address recipient) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "to" =
            some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hto]
  have hliqAfter :
      afterBranch.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "liquidity" =
            some (uniswapUint256Value liquidity)
    rw [store_get_self]
    simp [minFunctionResultValue, liquidity0, liquidity1, hliquidity]
  have hbalance0After :
      afterBranch.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "balance0" =
            some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance0]
  have hbalance1After :
      afterBranch.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "balance1" =
            some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance1]
  have hreserve0After :
      afterBranch.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "_reserve0" =
            some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0]
  have hreserve1After :
      afterBranch.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "_reserve1" =
            some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1]
  have hreserve0BaseAfter :
      afterBranch.locals.get? "reserve0" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "reserve0" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1BaseAfter :
      afterBranch.locals.get? "reserve1" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "reserve1" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1Base]
  have htail :
      ExecBlock config afterBranch evm
        ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
          updateReservesStmtsWith (.var "balance0") (.var "balance1")
            (.var "_reserve0") (.var "_reserve1"))
        (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
          (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
            balance0 balance1)) := by
    simpa [afterBranch, afterMint] using
      uniswapMintLiquidityMintUpdateElapsedZeroPrefix
        (locals := afterBranch.locals) evm recipient balance0 balance1 reserve0 reserve1
        liquidity htoAfter hliqAfter hbalance0After hbalance1After hreserve0After
        hreserve1After hreserve0BaseAfter hreserve1BaseAfter hliqNonzero hfitSupply
        hfitBalance hbound0 hbound1 helapsed
  simpa [List.append_assoc] using execBlock_append hbranch htail

theorem uniswapMintProportionalLiquidityUpdateCumulativePrefix
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 balance0 balance1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hfit0 : mintAmountProductNat amount0 totalSupply < UInt256.size)
    (hfit1 : mintAmountProductNat amount1 totalSupply < UInt256.size)
    (hreserve0Nonzero : reserve0 ≠ ⟨0⟩)
    (hreserve1Nonzero : reserve1 ≠ ⟨0⟩)
    (hliquidity :
      liquidity =
        minFunctionResultWord (mintProportionalLiquidityWord amount0 totalSupply reserve0)
          (mintProportionalLiquidityWord amount1 totalSupply reserve1))
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      0 < syncTimeElapsedInt (mintFunctionPostState evm recipient liquidity))
    (hreserve0Post :
      Int.ofNat reserve0.toNat ≠ 0)
    (hreserve1Post :
      Int.ofNat reserve1.toNat ≠ 0) :
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
    let afterMint := resumeAfterInternalCall afterBranch "_mintResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1"))
      (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
        (syncUpdateCumulativePackedReserveStateWith
          (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1)) := by
  intro liquidity0 liquidity1 afterBranch afterMint
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
  have htoAfter :
      afterBranch.locals.get? "to" = some (.address recipient) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "to" =
            some (.address recipient)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hto]
  have hliqAfter :
      afterBranch.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "liquidity" =
            some (uniswapUint256Value liquidity)
    rw [store_get_self]
    simp [minFunctionResultValue, liquidity0, liquidity1, hliquidity]
  have hbalance0After :
      afterBranch.locals.get? "balance0" = some (uniswapUint256Value balance0) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "balance0" =
            some (uniswapUint256Value balance0)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance0]
  have hbalance1After :
      afterBranch.locals.get? "balance1" = some (uniswapUint256Value balance1) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "balance1" =
            some (uniswapUint256Value balance1)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hbalance1]
  have hreserve0After :
      afterBranch.locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "_reserve0" =
            some (.int (Int.ofNat reserve0.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0]
  have hreserve1After :
      afterBranch.locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "_reserve1" =
            some (.int (Int.ofNat reserve1.toNat))
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1]
  have hreserve0BaseAfter :
      afterBranch.locals.get? "reserve0" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "reserve0" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1BaseAfter :
      afterBranch.locals.get? "reserve1" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "reserve1" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hreserve1Base]
  have htail :
      ExecBlock config afterBranch evm
        ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
          updateReservesStmtsWith (.var "balance0") (.var "balance1")
            (.var "_reserve0") (.var "_reserve1"))
        (.ok (resumeAfterInternalCall afterMint "_updateResult" none)
          (syncUpdateCumulativePackedReserveStateWith
            (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
            reserve1)) := by
    simpa [afterBranch, afterMint] using
      uniswapMintLiquidityMintUpdateCumulativePrefix
        (locals := afterBranch.locals) evm recipient balance0 balance1 reserve0 reserve1
        liquidity htoAfter hliqAfter hbalance0After hbalance1After hreserve0After
        hreserve1After hreserve0BaseAfter hreserve1BaseAfter hliqNonzero hfitSupply
        hfitBalance hbound0 hbound1 helapsed hreserve0Post hreserve1Post
  simpa [List.append_assoc] using execBlock_append hbranch htail

end UniswapV2Pair
