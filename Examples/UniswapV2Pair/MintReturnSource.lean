import Examples.UniswapV2Pair.MintLiquidityUpdateSource
open Solm ABI Ethereum Ethereum.EVM Reasoning.Theory Reasoning.Reach

set_option maxRecDepth 2000000

namespace UniswapV2Pair

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

end UniswapV2Pair
