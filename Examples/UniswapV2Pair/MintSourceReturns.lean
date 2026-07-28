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

theorem evalExpr_mint_feeOn_false
    {solm : Frame} (evm : EVM.State)
    (hfeeOn : solm.locals.get? "feeOn" = some (.bool false)) :
    evalExpr? config solm evm (.var "feeOn") = .ok (.bool false) := by
  simp only [evalExpr?, EvalResult.ofOption, hfeeOn]

theorem evalExpr_mint_feeOn_true
    {solm : Frame} (evm : EVM.State)
    (hfeeOn : solm.locals.get? "feeOn" = some (.bool true)) :
    evalExpr? config solm evm (.var "feeOn") = .ok (.bool true) := by
  simp only [evalExpr?, EvalResult.ofOption, hfeeOn]

theorem evalExpr_mint_liquidity_of_get
    {solm : Frame} (evm : EVM.State) (liquidity : UInt256)
    (hliq : solm.locals.get? "liquidity" = some (uniswapUint256Value liquidity)) :
    evalExpr? config solm evm (.var "liquidity") =
      .ok (uniswapUint256Value liquidity) := by
  simp only [evalExpr?, EvalResult.ofOption, hliq]

abbrev mintKLastProductValue (evm : EVM.State) : Value :=
  mintFeeReserveProductValue (uniswapReserve0Word evm) (uniswapReserve1Word evm)

abbrev mintKLastUpdatedState (evm : EVM.State) : EVM.State :=
  Solm.EVM.storageStore evm evm.executionEnv.codeOwner ⟨11⟩
    (mintFeeReserveProductWord (uniswapReserve0Word evm) (uniswapReserve1Word evm))

theorem evalExpr_mint_kLastReserveProduct_of_storage
    {locals : Store} (evm : EVM.State)
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hfit :
      mintFeeReserveProductNat (uniswapReserve0Word evm) (uniswapReserve1Word evm) <
        UInt256.size) :
    evalExpr? config { contract := contract, locals := locals } evm
      (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) =
        .ok (mintKLastProductValue evm) := by
  have hguard :
      ¬ (Int.ofNat (uniswapReserve0Word evm).toNat *
            Int.ofNat (uniswapReserve1Word evm).toNat < 0 ∨
          (2 : Int) ^ 256 ≤
            Int.ofNat (uniswapReserve0Word evm).toNat *
              Int.ofNat (uniswapReserve1Word evm).toNat) := by
    push Not
    constructor
    · exact Int.mul_nonneg (Int.natCast_nonneg _) (Int.natCast_nonneg _)
    · have hfitNat :
          (uniswapReserve0Word evm).toNat * (uniswapReserve1Word evm).toNat < 2 ^ 256 := by
        simpa [mintFeeReserveProductNat, UInt256.size] using hfit
      simpa [Nat.cast_mul] using Int.ofNat_lt.mpr hfitNat
  have hguardBool :
      ¬ ((decide (Int.ofNat (uniswapReserve0Word evm).toNat *
              Int.ofNat (uniswapReserve1Word evm).toNat < 0) ||
            decide (Int.ofNat (uniswapReserve0Word evm).toNat *
              Int.ofNat (uniswapReserve1Word evm).toNat ≥ (2 : Int) ^ 256)) = true) := by
    simpa [Bool.or_eq_true, ge_iff_le] using hguard
  have htoNat :
      (UInt256.ofNat
          (mintFeeReserveProductNat (uniswapReserve0Word evm) (uniswapReserve1Word evm))).toNat =
        mintFeeReserveProductNat (uniswapReserve0Word evm) (uniswapReserve1Word evm) := by
    exact ulit_toNat' _ hfit
  have htoNat' :
      (UInt256.ofNat
          ((uniswapReserve0Word evm).toNat * (uniswapReserve1Word evm).toNat)).toNat =
        (uniswapReserve0Word evm).toNat * (uniswapReserve1Word evm).toNat := by
    simpa [mintFeeReserveProductNat] using htoNat
  simp only [u256, evalExpr?, evalExpr_uniswap_reserve0 evm locals hreserve0Base,
    evalExpr_uniswap_reserve1 evm locals hreserve1Base, EvalResult.bind, bind, pure]
  simp only [evalBinaryOp?, uint256Int]
  rw [if_neg hguardBool]
  simp [mintKLastProductValue, mintFeeReserveProductValue, mintFeeReserveProductWord,
    mintFeeReserveProductNat, uniswapUint256Value, uint256Value, htoNat']

theorem mintAssignKLastProduct
    {locals : Store} (evm : EVM.State)
    (hkLastBase : locals.get? "kLast" = none) :
    assignStorageRef? config { contract := contract, locals := locals } evm .storage kLastRef
      (mintKLastProductValue evm) =
        .ok ({ contract := contract, locals := locals }, mintKLastUpdatedState evm) := by
  apply assignStorageRef_storage_scalar
      (er := ({ base := "kLast", steps := [] } : EvaledStorageRef))
      (ty := uint256St) (loc := uint256Loc ⟨11⟩)
  · simpa [kLastRef] using hkLastBase
  · simp [evalStorageRef, evalStorageRefSteps, kLastRef, EvalResult.bind, pure, bind]
  · simp [storageTypeAt?, contract, storageDecls, uint256St]
  · rfl
  · simpa [mintKLastUpdatedState, mintKLastProductValue, mintFeeReserveProductValue,
      uniswapUint256Value, uint256Value] using
      uniswapStorageLocStore_uint256 evm ⟨11⟩
        (mintFeeReserveProductWord (uniswapReserve0Word evm) (uniswapReserve1Word evm))

theorem uniswapMintAfterUpdateFeeOffReturn
    {locals : Store} (evm : EVM.State) (liquidity : UInt256)
    (hfeeOn : locals.get? "feeOn" = some (.bool false))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hunlockedBase : locals.get? "unlocked" = none) :
    ExecBlock config { contract := contract, locals := locals } evm
      ([ .ite (.var "feeOn")
          [ .assign .storage kLastRef
              (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
          [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned { contract := contract, locals := locals } (uniswapLockExitedState evm)
        (some [uniswapUint256Value liquidity])) := by
  have hfee :
      evalExpr? config { contract := contract, locals := locals } evm (.var "feeOn") =
        .ok (.bool false) :=
    evalExpr_mint_feeOn_false (solm := { contract := contract, locals := locals }) evm hfeeOn
  have hiteStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.ite (.var "feeOn")
          [ .assign .storage kLastRef
              (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
          [])
        (.ok { contract := contract, locals := locals } evm) :=
    ExecStmt.iteFalse hfee ExecBlock.nil
  have hite :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ]
        (.ok { contract := contract, locals := locals } evm) :=
    ExecBlock.consNormal hiteStmt ExecBlock.nil
  have hlock := uniswapLockExitSuffix evm locals hunlockedBase
  have hret :
      ExecBlock config { contract := contract, locals := locals } (uniswapLockExitedState evm)
        [ .return [.var "liquidity"] ]
        (.returned { contract := contract, locals := locals } (uniswapLockExitedState evm)
          (some [uniswapUint256Value liquidity])) :=
    ExecBlock.consReturn
      (ExecStmt.return
        (evalExprs?_singleton (evalExpr_mint_liquidity_of_get
          (solm := { contract := contract, locals := locals })
          (uniswapLockExitedState evm) liquidity hliq)))
  have htail := execBlock_append hlock hret
  simpa [List.append_assoc] using execBlock_append hite htail

theorem uniswapMintAfterUpdateFeeOnReturn
    {locals : Store} (evm : EVM.State) (liquidity : UInt256)
    (hfeeOn : locals.get? "feeOn" = some (.bool true))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hkLastBase : locals.get? "kLast" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
    (hfit :
      mintFeeReserveProductNat (uniswapReserve0Word evm) (uniswapReserve1Word evm) <
        UInt256.size) :
    ExecBlock config { contract := contract, locals := locals } evm
      ([ .ite (.var "feeOn")
          [ .assign .storage kLastRef
              (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
          [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned { contract := contract, locals := locals }
        (uniswapLockExitedState (mintKLastUpdatedState evm))
        (some [uniswapUint256Value liquidity])) := by
  have hfee :
      evalExpr? config { contract := contract, locals := locals } evm (.var "feeOn") =
        .ok (.bool true) :=
    evalExpr_mint_feeOn_true (solm := { contract := contract, locals := locals }) evm hfeeOn
  have hassignStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.assign .storage kLastRef
          (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))))
        (.ok { contract := contract, locals := locals } (mintKLastUpdatedState evm)) :=
    ExecStmt.assign
      (evalExpr_mint_kLastReserveProduct_of_storage evm hreserve0Base hreserve1Base hfit)
      (mintAssignKLastProduct evm hkLastBase)
  have htrueBranch :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .assign .storage kLastRef
            (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
        (.ok { contract := contract, locals := locals } (mintKLastUpdatedState evm)) :=
    ExecBlock.consNormal hassignStmt ExecBlock.nil
  have hiteStmt :
      ExecStmt config { contract := contract, locals := locals } evm
        (.ite (.var "feeOn")
          [ .assign .storage kLastRef
              (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
          [])
        (.ok { contract := contract, locals := locals } (mintKLastUpdatedState evm)) :=
    ExecStmt.iteTrue hfee htrueBranch
  have hite :
      ExecBlock config { contract := contract, locals := locals } evm
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ]
        (.ok { contract := contract, locals := locals } (mintKLastUpdatedState evm)) :=
    ExecBlock.consNormal hiteStmt ExecBlock.nil
  have hlock := uniswapLockExitSuffix (mintKLastUpdatedState evm) locals hunlockedBase
  have hret :
      ExecBlock config { contract := contract, locals := locals }
        (uniswapLockExitedState (mintKLastUpdatedState evm))
        [ .return [.var "liquidity"] ]
        (.returned { contract := contract, locals := locals }
          (uniswapLockExitedState (mintKLastUpdatedState evm))
          (some [uniswapUint256Value liquidity])) :=
    ExecBlock.consReturn
      (ExecStmt.return
        (evalExprs?_singleton (evalExpr_mint_liquidity_of_get
          (solm := { contract := contract, locals := locals })
          (uniswapLockExitedState (mintKLastUpdatedState evm)) liquidity hliq)))
  have htail := execBlock_append hlock hret
  simpa [List.append_assoc] using execBlock_append hite htail

theorem uniswapMintLiquidityMintUpdateElapsedZeroFeeOffReturn
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (balance0 balance1 reserve0 reserve1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : locals.get? "feeOn" = some (.bool false))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt (mintFunctionPostState evm recipient liquidity) = 0) :
    let afterMint :=
      resumeAfterInternalCall { contract := contract, locals := locals } "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
        .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
            balance0 balance1))
        (some [uniswapUint256Value liquidity])) := by
  intro afterMint afterUpdate
  have hprefix :=
    uniswapMintLiquidityMintUpdateElapsedZeroPrefix (locals := locals) evm recipient
      balance0 balance1 reserve0 reserve1 liquidity hto hliq hbalance0 hbalance1
      hreserve0 hreserve1 hreserve0Base hreserve1Base hliqNonzero hfitSupply hfitBalance
      hbound0 hbound1 helapsed
  have hfeeAfter :
      afterUpdate.locals.get? "feeOn" = some (.bool false) := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "feeOn" = some (.bool false)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hfeeOn]
  have hliqAfter :
      afterUpdate.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "liquidity" = some (uniswapUint256Value liquidity)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hliq]
  have hunlockedAfter :
      afterUpdate.locals.get? "unlocked" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "unlocked" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterUpdate
        (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
          balance0 balance1)
        ([ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
          lockExit ++
          [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
            (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
              balance0 balance1))
          (some [uniswapUint256Value liquidity])) := by
    simpa [afterUpdate] using
      uniswapMintAfterUpdateFeeOffReturn (locals := afterUpdate.locals)
        (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
          balance0 balance1)
        liquidity hfeeAfter hliqAfter hunlockedAfter
  simpa [List.append_assoc, afterMint, afterUpdate] using execBlock_append hprefix htail

theorem uniswapMintLiquidityMintUpdateElapsedZeroFeeOnReturn
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (balance0 balance1 reserve0 reserve1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : locals.get? "feeOn" = some (.bool true))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hkLastBase : locals.get? "kLast" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      syncTimeElapsedInt (mintFunctionPostState evm recipient liquidity) = 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
              balance0 balance1)) < UInt256.size) :
    let afterMint :=
      resumeAfterInternalCall { contract := contract, locals := locals } "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
        .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
              balance0 balance1)))
        (some [uniswapUint256Value liquidity])) := by
  intro afterMint afterUpdate
  have hprefix :=
    uniswapMintLiquidityMintUpdateElapsedZeroPrefix (locals := locals) evm recipient
      balance0 balance1 reserve0 reserve1 liquidity hto hliq hbalance0 hbalance1
      hreserve0 hreserve1 hreserve0Base hreserve1Base hliqNonzero hfitSupply hfitBalance
      hbound0 hbound1 helapsed
  have hfeeAfter :
      afterUpdate.locals.get? "feeOn" = some (.bool true) := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "feeOn" = some (.bool true)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hfeeOn]
  have hliqAfter :
      afterUpdate.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "liquidity" = some (uniswapUint256Value liquidity)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hliq]
  have hreserve0BaseAfter :
      afterUpdate.locals.get? "reserve0" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "reserve0" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1BaseAfter :
      afterUpdate.locals.get? "reserve1" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "reserve1" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hreserve1Base]
  have hkLastBaseAfter :
      afterUpdate.locals.get? "kLast" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "kLast" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hkLastBase]
  have hunlockedAfter :
      afterUpdate.locals.get? "unlocked" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "unlocked" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterUpdate
        (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
          balance0 balance1)
        ([ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
          lockExit ++
          [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
                balance0 balance1)))
          (some [uniswapUint256Value liquidity])) := by
    simpa [afterUpdate] using
      uniswapMintAfterUpdateFeeOnReturn (locals := afterUpdate.locals)
        (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
          balance0 balance1)
        liquidity hfeeAfter hliqAfter hreserve0BaseAfter hreserve1BaseAfter hkLastBaseAfter
        hunlockedAfter hfitKLast
  simpa [List.append_assoc, afterMint, afterUpdate] using execBlock_append hprefix htail

theorem uniswapMintLiquidityMintUpdateCumulativeFeeOffReturn
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (balance0 balance1 reserve0 reserve1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : locals.get? "feeOn" = some (.bool false))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
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
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
        .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveStateWith
            (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
            reserve1))
        (some [uniswapUint256Value liquidity])) := by
  intro afterMint afterUpdate
  have hprefix :=
    uniswapMintLiquidityMintUpdateCumulativePrefix (locals := locals) evm recipient
      balance0 balance1 reserve0 reserve1 liquidity hto hliq hbalance0 hbalance1
      hreserve0 hreserve1 hreserve0Base hreserve1Base hliqNonzero hfitSupply hfitBalance
      hbound0 hbound1 helapsed hreserve0Ne hreserve1Ne
  have hfeeAfter :
      afterUpdate.locals.get? "feeOn" = some (.bool false) := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "feeOn" = some (.bool false)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hfeeOn]
  have hliqAfter :
      afterUpdate.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "liquidity" = some (uniswapUint256Value liquidity)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hliq]
  have hunlockedAfter :
      afterUpdate.locals.get? "unlocked" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "unlocked" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterUpdate
        (syncUpdateCumulativePackedReserveStateWith
          (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1)
        ([ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
          lockExit ++
          [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
              reserve1))
          (some [uniswapUint256Value liquidity])) := by
    simpa [afterUpdate] using
      uniswapMintAfterUpdateFeeOffReturn (locals := afterUpdate.locals)
        (syncUpdateCumulativePackedReserveStateWith
          (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1)
        liquidity hfeeAfter hliqAfter hunlockedAfter
  simpa [List.append_assoc, afterMint, afterUpdate] using execBlock_append hprefix htail

theorem uniswapMintLiquidityMintUpdateCumulativeFeeOnReturn
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (balance0 balance1 reserve0 reserve1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (hliq : locals.get? "liquidity" = some (uniswapUint256Value liquidity))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : locals.get? "feeOn" = some (.bool true))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hkLastBase : locals.get? "kLast" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
    (hliqNonzero : liquidity ≠ ⟨0⟩)
    (hfitSupply : mintFunctionTotalSupplyNewNat evm liquidity < UInt256.size)
    (hfitBalance : mintFunctionToBalanceNewNat evm recipient liquidity < UInt256.size)
    (hbound0 : Int.ofNat balance0.toNat ≤ maxUint112)
    (hbound1 : Int.ofNat balance1.toNat ≤ maxUint112)
    (helapsed :
      0 < syncTimeElapsedInt (mintFunctionPostState evm recipient liquidity))
    (hreserve0Ne : Int.ofNat reserve0.toNat ≠ 0)
    (hreserve1Ne : Int.ofNat reserve1.toNat ≠ 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
              reserve1))
          (uniswapReserve1Word
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
              reserve1)) <
        UInt256.size) :
    let afterMint :=
      resumeAfterInternalCall { contract := contract, locals := locals } "_mintResult" none
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
        .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned afterUpdate
        (uniswapLockExitedState
            (mintKLastUpdatedState
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
              reserve1)))
        (some [uniswapUint256Value liquidity])) := by
  intro afterMint afterUpdate
  have hprefix :=
    uniswapMintLiquidityMintUpdateCumulativePrefix (locals := locals) evm recipient
      balance0 balance1 reserve0 reserve1 liquidity hto hliq hbalance0 hbalance1
      hreserve0 hreserve1 hreserve0Base hreserve1Base hliqNonzero hfitSupply hfitBalance
      hbound0 hbound1 helapsed hreserve0Ne hreserve1Ne
  have hfeeAfter :
      afterUpdate.locals.get? "feeOn" = some (.bool true) := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "feeOn" = some (.bool true)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hfeeOn]
  have hliqAfter :
      afterUpdate.locals.get? "liquidity" = some (uniswapUint256Value liquidity) := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "liquidity" = some (uniswapUint256Value liquidity)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hliq]
  have hreserve0BaseAfter :
      afterUpdate.locals.get? "reserve0" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "reserve0" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hreserve0Base]
  have hreserve1BaseAfter :
      afterUpdate.locals.get? "reserve1" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "reserve1" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hreserve1Base]
  have hkLastBaseAfter :
      afterUpdate.locals.get? "kLast" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "kLast" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hkLastBase]
  have hunlockedAfter :
      afterUpdate.locals.get? "unlocked" = none := by
    change ((locals.insert "_mintResult" Value.unit).insert "_updateResult" Value.unit).get?
      "unlocked" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterUpdate
        (syncUpdateCumulativePackedReserveStateWith
          (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1)
        ([ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
          lockExit ++
          [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdateCumulativePackedReserveStateWith
                (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
                reserve1)))
          (some [uniswapUint256Value liquidity])) := by
    simpa [afterUpdate] using
      uniswapMintAfterUpdateFeeOnReturn (locals := afterUpdate.locals)
        (syncUpdateCumulativePackedReserveStateWith
          (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0 reserve1)
        liquidity hfeeAfter hliqAfter hreserve0BaseAfter hreserve1BaseAfter hkLastBaseAfter
        hunlockedAfter hfitKLast
  simpa [List.append_assoc, afterMint, afterUpdate] using execBlock_append hprefix htail

theorem uniswapMintProportionalLiquidityUpdateElapsedZeroFeeOffReturn
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 balance0 balance1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : locals.get? "feeOn" = some (.bool false))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
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
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned afterUpdate
        (uniswapLockExitedState
          (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
            balance0 balance1))
        (some [uniswapUint256Value liquidity])) := by
  intro liquidity0 liquidity1 afterBranch afterMint afterUpdate
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
  have hfeeOnAfter :
      afterBranch.locals.get? "feeOn" = some (.bool false) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "feeOn" =
            some (.bool false)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hfeeOn]
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
  have hunlockedBaseAfter :
      afterBranch.locals.get? "unlocked" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "unlocked" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterBranch evm
        ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
          updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
          [ .ite (.var "feeOn")
              [ .assign .storage kLastRef
                  (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
              [] ] ++
          lockExit ++
          [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
            (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
              balance0 balance1))
          (some [uniswapUint256Value liquidity])) := by
    simpa [afterBranch, afterMint, afterUpdate] using
      uniswapMintLiquidityMintUpdateElapsedZeroFeeOffReturn
        (locals := afterBranch.locals) evm recipient balance0 balance1 reserve0 reserve1
        liquidity htoAfter hliqAfter hbalance0After hbalance1After hfeeOnAfter
        hreserve0After hreserve1After hreserve0BaseAfter hreserve1BaseAfter
        hunlockedBaseAfter hliqNonzero hfitSupply hfitBalance hbound0 hbound1 helapsed
  simpa [List.append_assoc] using execBlock_append hbranch htail

theorem uniswapMintProportionalLiquidityUpdateCumulativeFeeOffReturn
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 balance0 balance1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : locals.get? "feeOn" = some (.bool false))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
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
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
          (syncUpdateCumulativePackedReserveStateWith
            (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
            reserve1))
        (some [uniswapUint256Value liquidity])) := by
  intro liquidity0 liquidity1 afterBranch afterMint afterUpdate
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
  have hfeeOnAfter :
      afterBranch.locals.get? "feeOn" = some (.bool false) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "feeOn" =
            some (.bool false)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hfeeOn]
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
  have hunlockedBaseAfter :
      afterBranch.locals.get? "unlocked" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "unlocked" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterBranch evm
        ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
          updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
          [ .ite (.var "feeOn")
              [ .assign .storage kLastRef
                  (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
              [] ] ++
          lockExit ++
          [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
              reserve1))
          (some [uniswapUint256Value liquidity])) := by
    simpa [afterBranch, afterMint, afterUpdate] using
      uniswapMintLiquidityMintUpdateCumulativeFeeOffReturn
        (locals := afterBranch.locals) evm recipient balance0 balance1 reserve0 reserve1
        liquidity htoAfter hliqAfter hbalance0After hbalance1After hfeeOnAfter
        hreserve0After hreserve1After hreserve0BaseAfter hreserve1BaseAfter
        hunlockedBaseAfter hliqNonzero hfitSupply hfitBalance hbound0 hbound1 helapsed
        hreserve0Post hreserve1Post
  simpa [List.append_assoc] using execBlock_append hbranch htail

theorem uniswapMintProportionalLiquidityUpdateElapsedZeroFeeOnReturn
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 balance0 balance1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : locals.get? "feeOn" = some (.bool true))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hkLastBase : locals.get? "kLast" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
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
      syncTimeElapsedInt (mintFunctionPostState evm recipient liquidity) = 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
              balance0 balance1))
          (uniswapReserve1Word
            (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
              balance0 balance1)) < UInt256.size) :
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
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
              balance0 balance1)))
        (some [uniswapUint256Value liquidity])) := by
  intro liquidity0 liquidity1 afterBranch afterMint afterUpdate
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
  have hfeeOnAfter :
      afterBranch.locals.get? "feeOn" = some (.bool true) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "feeOn" =
            some (.bool true)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hfeeOn]
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
  have hkLastBaseAfter :
      afterBranch.locals.get? "kLast" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "kLast" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hkLastBase]
  have hunlockedBaseAfter :
      afterBranch.locals.get? "unlocked" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "unlocked" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterBranch evm
        ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
          updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
          [ .ite (.var "feeOn")
              [ .assign .storage kLastRef
                  (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
              [] ] ++
          lockExit ++
          [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdatePackedReserveState (mintFunctionPostState evm recipient liquidity)
                balance0 balance1)))
          (some [uniswapUint256Value liquidity])) := by
    simpa [afterBranch, afterMint, afterUpdate] using
      uniswapMintLiquidityMintUpdateElapsedZeroFeeOnReturn
        (locals := afterBranch.locals) evm recipient balance0 balance1 reserve0 reserve1
        liquidity htoAfter hliqAfter hbalance0After hbalance1After hfeeOnAfter
        hreserve0After hreserve1After hreserve0BaseAfter hreserve1BaseAfter
        hkLastBaseAfter hunlockedBaseAfter hliqNonzero hfitSupply hfitBalance hbound0
        hbound1 helapsed hfitKLast
  simpa [List.append_assoc] using execBlock_append hbranch htail

theorem uniswapMintProportionalLiquidityUpdateCumulativeFeeOnReturn
    {locals : Store} (evm : EVM.State) (recipient : AccountAddress)
    (amount0 amount1 totalSupply reserve0 reserve1 balance0 balance1 liquidity : UInt256)
    (hto : locals.get? "to" = some (.address recipient))
    (htotal : locals.get? "_totalSupply" = some (uniswapUint256Value totalSupply))
    (htotalNonzero : totalSupply ≠ ⟨0⟩)
    (hamount0 : locals.get? "amount0" = some (uniswapUint256Value amount0))
    (hamount1 : locals.get? "amount1" = some (uniswapUint256Value amount1))
    (hbalance0 : locals.get? "balance0" = some (uniswapUint256Value balance0))
    (hbalance1 : locals.get? "balance1" = some (uniswapUint256Value balance1))
    (hfeeOn : locals.get? "feeOn" = some (.bool true))
    (hreserve0 : locals.get? "_reserve0" = some (.int (Int.ofNat reserve0.toNat)))
    (hreserve1 : locals.get? "_reserve1" = some (.int (Int.ofNat reserve1.toNat)))
    (hreserve0Base : locals.get? "reserve0" = none)
    (hreserve1Base : locals.get? "reserve1" = none)
    (hkLastBase : locals.get? "kLast" = none)
    (hunlockedBase : locals.get? "unlocked" = none)
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
      Int.ofNat reserve1.toNat ≠ 0)
    (hfitKLast :
      mintFeeReserveProductNat
          (uniswapReserve0Word
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
              reserve1))
          (uniswapReserve1Word
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
              reserve1)) <
        UInt256.size) :
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
    let afterUpdate := resumeAfterInternalCall afterMint "_updateResult" none
    ExecBlock config { contract := contract, locals := locals } evm
      ([mintLiquidityBranchStmt] ++
        [ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
        updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
        [ .ite (.var "feeOn")
            [ .assign .storage kLastRef
                (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
            [] ] ++
        lockExit ++
        [ .return [.var "liquidity"] ])
      (.returned afterUpdate
        (uniswapLockExitedState
          (mintKLastUpdatedState
            (syncUpdateCumulativePackedReserveStateWith
              (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
              reserve1)))
        (some [uniswapUint256Value liquidity])) := by
  intro liquidity0 liquidity1 afterBranch afterMint afterUpdate
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
  have hfeeOnAfter :
      afterBranch.locals.get? "feeOn" = some (.bool true) := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "feeOn" =
            some (.bool true)
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hfeeOn]
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
  have hkLastBaseAfter :
      afterBranch.locals.get? "kLast" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "kLast" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hkLastBase]
  have hunlockedBaseAfter :
      afterBranch.locals.get? "unlocked" = none := by
    change (((locals.insert "liquidity0"
      (mintProportionalLiquidityValue amount0 totalSupply reserve0)).insert "liquidity1"
        (mintProportionalLiquidityValue amount1 totalSupply reserve1)).insert "liquidity"
          (minFunctionResultValue liquidity0 liquidity1)).get? "unlocked" = none
    rw [store_get_ne _ _ (by decide), store_get_ne _ _ (by decide),
      store_get_ne _ _ (by decide), hunlockedBase]
  have htail :
      ExecBlock config afterBranch evm
        ([ .require (.binary .gt (.var "liquidity") (.intLit 0)),
          .internalCall "_mint" [.var "to", .var "liquidity"] "_mintResult" ] ++
          updateReservesStmtsWith (.var "balance0") (.var "balance1")
          (.var "_reserve0") (.var "_reserve1") ++
          [ .ite (.var "feeOn")
              [ .assign .storage kLastRef
                  (u256 (.binary .mul (.storage reserve0Ref) (.storage reserve1Ref))) ]
              [] ] ++
          lockExit ++
          [ .return [.var "liquidity"] ])
        (.returned afterUpdate
          (uniswapLockExitedState
            (mintKLastUpdatedState
              (syncUpdateCumulativePackedReserveStateWith
                (mintFunctionPostState evm recipient liquidity) balance0 balance1 reserve0
                reserve1)))
          (some [uniswapUint256Value liquidity])) := by
    simpa [afterBranch, afterMint, afterUpdate] using
      uniswapMintLiquidityMintUpdateCumulativeFeeOnReturn
        (locals := afterBranch.locals) evm recipient balance0 balance1 reserve0 reserve1
        liquidity htoAfter hliqAfter hbalance0After hbalance1After hfeeOnAfter
        hreserve0After hreserve1After hreserve0BaseAfter hreserve1BaseAfter
        hkLastBaseAfter hunlockedBaseAfter hliqNonzero hfitSupply hfitBalance hbound0
        hbound1 helapsed hreserve0Post hreserve1Post hfitKLast
  simpa [List.append_assoc] using execBlock_append hbranch htail

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
