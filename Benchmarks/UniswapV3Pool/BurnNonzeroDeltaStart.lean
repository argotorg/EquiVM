import Benchmarks.UniswapV3Pool.BurnPositionUpdate

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev burnBlockTimestamp32Value (I : ExecutionEnv) : Value :=
  .int (Int.ofNat ((UInt256.ofNat I.header.timestamp).toNat % 2 ^ (32 : Nat)))

abbrev burnModifyPositionAfterTimeFrame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.insert
      "time" (burnBlockTimestamp32Value I) }

theorem burnEvalBlockTimestamp32AfterFeeGlobals {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I) blockTimestamp32 =
      .ok (burnBlockTimestamp32Value I) := by
  unfold blockTimestamp32 uint32Wrap modE uint32Modulus burnBlockTimestamp32Value
  simp only [evalExpr?, envValue, initState, EvalResult.bind, bind, pure, evalBinaryOp?]
  norm_num

theorem uniswapV3PoolModifyPositionSourceLiquidityDeltaNonzeroTimeStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩) :
    ExecStmt (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
        [.letDecl "time" (some uint32) blockTimestamp32] [])
      (ExecResult.ok (burnModifyPositionAfterTimeFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  refine ExecStmt.iteTrue ?_ ?_
  · exact burnEvalLiquidityDeltaNeZeroTrue (v := v) (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hnonzero
  · exact ExecBlock.consNormal
      (ExecStmt.letDecl (burnEvalBlockTimestamp32AfterFeeGlobals (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g)))
      ExecBlock.nil

abbrev burnPoolLiquidityWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I ⟨4⟩) uint128Mask

abbrev burnPoolLiquidityValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnPoolLiquidityWord σ I).toNat)

abbrev burnObserveSingleArgValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [ burnBlockTimestamp32Value I, .int 0, burnSlot0TickValue σ I,
    burnSlot0ObservationIndexValue σ I, burnPoolLiquidityValue σ I,
    burnSlot0ObservationCardinalityValue σ I ]

abbrev burnObserveSingleStore (σ : AccountMap) (I : ExecutionEnv) : Store :=
  ((((((∅ : Store)
    |>.insert "cardinality" (burnSlot0ObservationCardinalityValue σ I))
    |>.insert "liquidity" (burnPoolLiquidityValue σ I))
    |>.insert "index" (burnSlot0ObservationIndexValue σ I))
    |>.insert "tick" (burnSlot0TickValue σ I))
    |>.insert "secondsAgo" (.int 0))
    |>.insert "time" (burnBlockTimestamp32Value I)

theorem burnObserveSingleStore_secondsAgo (σ : AccountMap) (I : ExecutionEnv) :
    (burnObserveSingleStore σ I).get? "secondsAgo" = some (.int 0) := by
  rw [burnObserveSingleStore]
  rw [store_get_ne
    (L := (((((∅ : Store).insert "cardinality" (burnSlot0ObservationCardinalityValue σ I))
      |>.insert "liquidity" (burnPoolLiquidityValue σ I))
      |>.insert "index" (burnSlot0ObservationIndexValue σ I))
      |>.insert "tick" (burnSlot0TickValue σ I))
      |>.insert "secondsAgo" (.int 0))
    (k := "time") (a := "secondsAgo") (burnBlockTimestamp32Value I)
    (by native_decide)]
  exact store_get_self
    ((((∅ : Store).insert "cardinality" (burnSlot0ObservationCardinalityValue σ I))
      |>.insert "liquidity" (burnPoolLiquidityValue σ I))
      |>.insert "index" (burnSlot0ObservationIndexValue σ I)
      |>.insert "tick" (burnSlot0TickValue σ I))
    "secondsAgo" (.int 0)

theorem burnObserveSingleStore_index (σ : AccountMap) (I : ExecutionEnv) :
    (burnObserveSingleStore σ I).get? "index" =
      some (burnSlot0ObservationIndexValue σ I) := by
  rw [burnObserveSingleStore]
  rw [store_get_ne3
    (L := (((∅ : Store).insert "cardinality" (burnSlot0ObservationCardinalityValue σ I))
      |>.insert "liquidity" (burnPoolLiquidityValue σ I))
      |>.insert "index" (burnSlot0ObservationIndexValue σ I))
    (k1 := "tick") (k2 := "secondsAgo") (k3 := "time") (a := "index")
    (burnSlot0TickValue σ I) (.int 0) (burnBlockTimestamp32Value I)
    (by native_decide) (by native_decide) (by native_decide)]
  exact store_get_self
    (((∅ : Store).insert "cardinality" (burnSlot0ObservationCardinalityValue σ I))
      |>.insert "liquidity" (burnPoolLiquidityValue σ I))
    "index" (burnSlot0ObservationIndexValue σ I)

theorem burnObserveSingleStore_observations (σ : AccountMap) (I : ExecutionEnv) :
    (burnObserveSingleStore σ I).get? "observations" = none := by
  rw [burnObserveSingleStore]
  rw [store_get_ne5
    (L := ((∅ : Store).insert "cardinality" (burnSlot0ObservationCardinalityValue σ I)))
    (k1 := "liquidity") (k2 := "index") (k3 := "tick")
    (k4 := "secondsAgo") (k5 := "time") (a := "observations")
    (burnPoolLiquidityValue σ I) (burnSlot0ObservationIndexValue σ I)
    (burnSlot0TickValue σ I) (.int 0) (burnBlockTimestamp32Value I)
    (by native_decide) (by native_decide) (by native_decide)
    (by native_decide) (by native_decide)]
  rw [store_get_ne (L := (∅ : Store)) (k := "cardinality") (a := "observations")
    (burnSlot0ObservationCardinalityValue σ I) (by native_decide)]
  simp

theorem burnEvalLiquidity {v : PoolImmutables}
    {L : Store} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbase : L.get? "liquidity" = none) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I) (.storage liquidityRef) =
      .ok (burnPoolLiquidityValue σ I) := by
  apply evalExpr_storage_scalar_value
      (er := { base := "liquidity", steps := [] })
      (t := .int uint128Int)
      (loc := loc ⟨4⟩ ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide) (.int uint128Int))
  · simpa [liquidityRef] using hbase
  · simp [evalStorageRef, liquidityRef, pure, bind, EvalResult.bind]
  · simp [contract, storageDecls, storageTypeAt?, uint128St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc]
  · simpa [initState, burnPoolLiquidityValue, burnPoolLiquidityWord, solcSlotWord, loc] using
      (storageLocLoad_uint_offset0 (initState cA gh bl σ σ₀ g A I) ⟨4⟩
        ⟨16, by decide⟩ ⟨128, by decide⟩ (hbound := by decide) (by decide))

theorem burnModifyPosition_evalObserveSingleArgs {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExprs? (config v) (burnModifyPositionAfterTimeFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .var "time", .intLit 0, .storage (slot0F "tick"),
        .storage (slot0F "observationIndex"), .storage liquidityRef,
        .storage (slot0F "observationCardinality") ] =
      .ok (burnObserveSingleArgValues σ I) := by
  have htime :
      (burnModifyPositionAfterTimeFrame v σ I).locals.get? "time" =
        some (burnBlockTimestamp32Value I) := by
    simp
  have hslot0 : (burnModifyPositionAfterTimeFrame v σ I).locals.get? "slot0" = none := by
    simp [burnModifyPositionStore]
  have hliq : (burnModifyPositionAfterTimeFrame v σ I).locals.get? "liquidity" = none := by
    simp [burnModifyPositionStore]
  have htick := burnEvalSlot0Tick (v := v)
    (L := (burnModifyPositionAfterTimeFrame v σ I).locals)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hslot0
  have hindex := burnEvalSlot0ObservationIndex (v := v)
    (L := (burnModifyPositionAfterTimeFrame v σ I).locals)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hslot0
  have hcard := burnEvalSlot0ObservationCardinality (v := v)
    (L := (burnModifyPositionAfterTimeFrame v σ I).locals)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hslot0
  have hliquidity := burnEvalLiquidity (v := v)
    (L := (burnModifyPositionAfterTimeFrame v σ I).locals)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
    (g := g) hliq
  simp [evalExprs?, evalExpr?, EvalResult.ofOption, EvalResult.bind, bind, pure,
    htick, hindex, hliquidity, hcard, burnObserveSingleArgValues]

theorem burnObserveSingle_bindParams (σ : AccountMap) (I : ExecutionEnv) :
    bindParams? observeSingleFunction.params (burnObserveSingleArgValues σ I) =
      some (burnObserveSingleStore σ I) := by
  rfl

theorem uniswapV3PoolLookupObserveSingle (v : PoolImmutables) :
    lookupCallable? (contract v) "observeSingle" = some observeSingleFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
    getTickAtSqrtRatioFunction, oracleLteFunction, oracleTransformFunction,
    getSurroundingObservationsFunction, observeSingleFunction, observeBodyFunction,
    liquidityAddDeltaFunction, oracleWriteFunction, tickGetFeeGrowthInsideFunction,
    tickUpdateFunction, tickClearFunction, tickBitmapFlipFunction, positionUpdateFunction,
    getAmount0DeltaUnsignedFunction, getAmount1DeltaUnsignedFunction,
    getAmount0DeltaSignedFunction, getAmount1DeltaSignedFunction, modifyPositionFunction]

theorem burnObserveSingleEvalSecondsAgoZero {v : PoolImmutables} {σ I evm} :
    evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I } evm
      (eqE (.var "secondsAgo") (.intLit 0)) = .ok (.bool true) := by
  unfold eqE
  simp only [evalExpr?, EvalResult.bind, bind, pure]
  rw [burnObserveSingleStore_secondsAgo]
  rfl

theorem burnObserveSingleEvalIndex {v : PoolImmutables} {σ I evm} :
    evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I } evm
      (.var "index") = .ok (burnSlot0ObservationIndexValue σ I) := by
  simp only [evalExpr?]
  rw [burnObserveSingleStore_index]
  rfl

theorem burnObserveSingleEvalIndexLtBoundFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hoob : 65535 ≤ (slot0ObservationIndexWord σ I).toNat) :
    evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I }
      (initState cA gh bl σ σ₀ g A I) (ltE (.var "index") (.intLit 65535)) =
        .ok (.bool false) := by
  unfold ltE
  simp only [evalExpr?, burnObserveSingleEvalIndex, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hnot : ¬ Int.ofNat (slot0ObservationIndexWord σ I).toNat < (65535 : Int) := by
    intro hlt
    have hltNat : (slot0ObservationIndexWord σ I).toNat < 65535 := by
      exact Int.ofNat_lt.mp hlt
    exact not_lt_of_ge hoob hltNat
  rw [show decide (Int.ofNat (slot0ObservationIndexWord σ I).toNat < 65535) = false from
    decide_eq_false hnot]

theorem burnObserveSingleEvalIndexLtBoundTrue {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbound : (slot0ObservationIndexWord σ I).toNat < 65535) :
    evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I }
      (initState cA gh bl σ σ₀ g A I) (ltE (.var "index") (.intLit 65535)) =
        .ok (.bool true) := by
  unfold ltE
  simp only [evalExpr?, burnObserveSingleEvalIndex, EvalResult.bind, bind, pure, evalBinaryOp?]
  have hlt : Int.ofNat (slot0ObservationIndexWord σ I).toNat < (65535 : Int) := by
    change ((slot0ObservationIndexWord σ I).toNat : Int) < (65535 : Int)
    exact_mod_cast hbound
  rw [show decide (Int.ofNat (slot0ObservationIndexWord σ I).toNat < 65535) = true from
    decide_eq_true hlt]

theorem uniswapV3PoolObserveSingleSourceIndexOobReverts {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hoob : 65535 ≤ (slot0ObservationIndexWord σ I).toNat) :
    ExecFuncBody (config v)
      { contract := contract v, locals := burnObserveSingleStore σ I }
      (initState cA gh bl σ σ₀ g A I) observeSingleFunction.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  simpa [observeSingleFunction] using
    (ExecBlock.consRevert
      (ExecStmt.iteTrue (burnObserveSingleEvalSecondsAgoZero (v := v) (σ := σ) (I := I)
        (evm := initState cA gh bl σ σ₀ g A I))
        (ExecBlock.consRevert
          (ExecStmt.requireFalse (burnObserveSingleEvalIndexLtBoundFalse (v := v)
            (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
            (I := I) (g := g) hoob)))))

private def burnModifyPositionObserveSingleOobTail (_v : PoolImmutables) : List Stmt :=
  [ .internalCall "tickGetFeeGrowthInside"
      [ .var "tickLower", .var "tickUpper", .var "_slot0tick",
        .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128" ]
      "feeGrowthInside",
    .internalCall "positionUpdate"
      [ .var "_positionKey", .var "liquidityDelta", tuple0 (.var "feeGrowthInside"),
        tuple1 (.var "feeGrowthInside") ]
      "_positionUpdated",
    Stmt.ite (ltE (.var "liquidityDelta") (.intLit 0))
      [ Stmt.ite (.var "flippedLower")
          [ .internalCall "tickClear" [.var "tickLower"] "_clearLower" ]
          [],
        Stmt.ite (.var "flippedUpper")
          [ .internalCall "tickClear" [.var "tickUpper"] "_clearUpper" ]
          [] ]
      [],
    .letDecl "amount0" (some int256) (.intLit 0),
    .letDecl "amount1" (some int256) (.intLit 0),
    Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
      [ Stmt.ite (ltE (.var "_slot0tick") (.var "tickLower"))
          [ .internalCall "getSqrtRatioAtTick" [.var "tickLower"] "sqrtRatioLowerBelow",
            .internalCall "getSqrtRatioAtTick" [.var "tickUpper"] "sqrtRatioUpperBelow",
            .internalCall "getAmount0DeltaSigned"
              [ .var "sqrtRatioLowerBelow", .var "sqrtRatioUpperBelow",
                .var "liquidityDelta" ]
              "amount0Below",
            .assign .localVar (varRef "amount0") (.var "amount0Below") ]
          [ Stmt.ite (ltE (.var "_slot0tick") (.var "tickUpper"))
              [ .letDecl "liquidityBefore" (some uint128) (.storage liquidityRef),
                .internalCall "oracleWrite"
                  [ .var "_slot0observationIndex", blockTimestamp32, .var "_slot0tick",
                    .var "liquidityBefore", .var "_slot0observationCardinality",
                    .var "_slot0observationCardinalityNext" ]
                  "oracleUpdated",
                .assign .storage (slot0F "observationIndex") (tuple0 (.var "oracleUpdated")),
                .assign .storage (slot0F "observationCardinality")
                  (tuple1 (.var "oracleUpdated")),
                .internalCall "getSqrtRatioAtTick" [.var "tickUpper"]
                  "sqrtRatioUpperInside",
                .internalCall "getAmount0DeltaSigned"
                  [ .var "_slot0sqrtPriceX96", .var "sqrtRatioUpperInside",
                    .var "liquidityDelta" ]
                  "amount0Inside",
                .assign .localVar (varRef "amount0") (.var "amount0Inside"),
                .internalCall "getSqrtRatioAtTick" [.var "tickLower"]
                  "sqrtRatioLowerInside",
                .internalCall "getAmount1DeltaSigned"
                  [ .var "sqrtRatioLowerInside", .var "_slot0sqrtPriceX96",
                    .var "liquidityDelta" ]
                  "amount1Inside",
                .assign .localVar (varRef "amount1") (.var "amount1Inside"),
                .internalCall "liquidityAddDelta"
                  [ .var "liquidityBefore", .var "liquidityDelta" ]
                  "liquidityAfter",
                .assign .storage liquidityRef (.var "liquidityAfter") ]
              [ .internalCall "getSqrtRatioAtTick" [.var "tickLower"]
                  "sqrtRatioLowerAbove",
                .internalCall "getSqrtRatioAtTick" [.var "tickUpper"]
                  "sqrtRatioUpperAbove",
                .internalCall "getAmount1DeltaSigned"
                  [ .var "sqrtRatioLowerAbove", .var "sqrtRatioUpperAbove",
                    .var "liquidityDelta" ]
                  "amount1Above",
                .assign .localVar (varRef "amount1") (.var "amount1Above") ] ] ]
      [],
    .return [.var "_positionKey", .var "amount0", .var "amount1"] ]

theorem uniswapV3PoolModifyPositionSourceObserveSingleOobReverts
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hoob : 65535 ≤ (slot0ObservationIndexWord σ I).toNat) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolModifyPositionSourceThroughFeeGrowthGlobals (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge hle
  have hstep : ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (burnModifyPositionLiquidityDeltaUpdateStep v) .reverted := by
    refine ExecBlock.consRevert ?_
    refine ExecStmt.iteTrue ?_ ?_
    · exact burnEvalLiquidityDeltaNeZeroTrue (v := v) (cA := cA) (gh := gh)
        (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hnonzero
    · refine ExecBlock.consNormal
        (solm' := burnModifyPositionAfterTimeFrame v σ I)
        (evm' := initState cA gh bl σ σ₀ g A I) ?_ ?_
      · exact ExecStmt.letDecl (burnEvalBlockTimestamp32AfterFeeGlobals (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g))
      · refine ExecBlock.consRevert ?_
        refine internalCallFunctionRevert (callee := observeSingleFunction)
          (argVals := burnObserveSingleArgValues σ I)
          (locals := burnObserveSingleStore σ I) ?_ ?_ ?_ ?_
        · exact burnModifyPosition_evalObserveSingleArgs (v := v) (cA := cA)
            (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
            (g := g)
        · simpa [burnModifyPositionAfterTimeFrame] using uniswapV3PoolLookupObserveSingle v
        · exact burnObserveSingle_bindParams σ I
        · simpa [burnModifyPositionAfterTimeFrame] using
            uniswapV3PoolObserveSingleSourceIndexOobReverts (v := v) (cA := cA)
              (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
              (g := g) hoob
  have hmid := execBlock_append hprefix hstep
  have hfull :=
    execBlock_append_term (s2 := burnModifyPositionObserveSingleOobTail v) hmid (by
      intro f e h
      cases h)
  simpa [modifyPositionFunction, burnModifyPositionSlot0Prefix,
    burnModifyPositionPositionKeyStep, burnModifyPositionFeeGrowthGlobalsStep,
    burnModifyPositionLiquidityDeltaUpdateStep, burnModifyPositionObserveSingleOobTail]
    using hfull

theorem uniswapV3PoolBurnSourceObserveSingleOobReverts
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hoob :
      65535 ≤
        (slot0ObservationIndexWord
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I).toNat) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I)
      burnTransition.body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolBurnSourceThroughLiquidityDelta (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked hcanon
  have hlockState :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I) =
        initState cA gh bl
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
          σ₀ g A I := by
    unfold Solm.EVM.storageStore State.lookupAccount sstoreAccountMap
    cases hlookup : σ.find? I.codeOwner with
    | none =>
        simp [initState, Option.option, hlookup]
    | some _ =>
        simp [initState, State.setAccount, Account.updateStorage, Option.option, hlookup]
  have hstmt :
      ExecStmt (config v) (burnLiquidityDeltaFrame v I)
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))
        (.internalCall "modifyPosition"
          [.env .caller, .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
          "modified")
        .reverted := by
    rw [hlockState]
    refine internalCallFunctionRevert (callee := modifyPositionFunction v)
      (argVals := burnModifyPositionArgValues I) (locals := burnModifyPositionStore I)
      ?_ ?_ ?_ ?_
    · have hLower := burnLiquidityDeltaFrame_tickLower (v := v) I
      have hUpper := burnLiquidityDeltaFrame_tickUpper (v := v) I
      have hDelta := burnLiquidityDeltaFrame_liquidityDelta (v := v) I
      simp only [burnModifyPositionArgValues, evalExprs?, evalExpr?, envValue, initState,
        EvalResult.bind, bind, pure]
      rw [hLower, hUpper, hDelta]
      rfl
    · simpa [burnLiquidityDeltaFrame] using uniswapV3PoolLookupModifyPosition v
    · rfl
    · exact uniswapV3PoolModifyPositionSourceObserveSingleOobReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl)
        (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hguard htickLt hge hle hnonzero hoob
  simpa [burnTransition, nonpayable, lockPrefix] using
    execBlock_append hprefix (ExecBlock.consRevert hstmt)

private theorem uniswapV3PoolBurnNonzeroTimestampDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 11291 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 15650) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 15650 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl
      all_goals omega)

private theorem uniswapV3PoolBurnNonzeroStartDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 19189 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl
      all_goals omega)

private theorem uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 13193 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13241) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 13241 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl
      all_goals omega)

private theorem uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 13208 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13274) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 13274 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl
      all_goals omega)

private theorem uniswapV3PoolBurnNonzeroShortPatchDisjoint {v : PoolImmutables}
    {pc : UInt256} {n : Nat} (hlo : 19189 ≤ pc.toNat) (hhi : pc.toNat + n ≤ 19295) :
    ∀ p ∈ patches v, pc.toNat + n ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
    List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

private theorem uniswapV3PoolBurnNonzeroDecodePatchedPush1 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 2 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 2 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x60)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1)) = n) :
    decode code pc = some (.Push .PUSH1, some (n, 1)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 1) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 1) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 1 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 1)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x60 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x60 : UInt8) >>= parseInstr) = some (.Push .PUSH1) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH1,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 1)), 1)) =
    some (Operation.Push Operation.POp.PUSH1, some (n, 1))
  rw [hextract, hval]

private theorem uniswapV3PoolBurnNonzeroDecodePatchedPush2 {v : PoolImmutables}
    {code : ByteArray} {pc n : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hwin : pc.toNat + 3 ≤ uniswapV3PoolBytecode.size)
    (hdisj : ∀ p ∈ patches v, pc.toNat + 3 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat)
    (hgetTemplate : uniswapV3PoolBytecode.get? pc.toNat = some 0x61)
    (hval : uInt256OfByteArray
        (uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2)) = n) :
    decode code pc = some (.Push .PUSH2, some (n, 2)) := by
  have hsize := uniswapV3PoolPatchedSize hpatch
  have htemplate64 : uniswapV3PoolBytecode.size < 2 ^ 64 := by native_decide
  have hget : code.get? pc.toNat = uniswapV3PoolBytecode.get? pc.toNat := by
    apply get?_eq_of_extract_one
    · rw [hsize]
      omega
    · omega
    · exact patchRuntime_extract_eq (start := pc.toNat) (stop := pc.toNat + 1)
        (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
        (by omega) (by omega)
        (fun p hp => by
          rcases hdisj p hp with hbefore | hafter
          · exact Or.inl (by omega)
          · exact Or.inr hafter)
        hpatch
  have hextract :
      code.extract' pc.toNat.succ (pc.toNat.succ + 2) =
        uniswapV3PoolBytecode.extract' pc.toNat.succ (pc.toNat.succ + 2) := by
    unfold ByteArray.extract'
    have hguard :
        (decide (pc.toNat.succ < 2 ^ 64) && decide (pc.toNat.succ + 2 < 2 ^ 64)) =
          true := by
      rw [Bool.and_eq_true]
      constructor <;> rw [decide_eq_true_eq] <;> omega
    rw [if_pos hguard, if_pos hguard]
    exact patchRuntime_extract_eq (start := pc.toNat.succ) (stop := pc.toNat.succ + 2)
      (template := uniswapV3PoolBytecode) (out := code) (ps := patches v)
      (by omega) (by omega)
      (fun p hp => by
        rcases hdisj p hp with hbefore | hafter
        · exact Or.inl hbefore
        · exact Or.inr (by omega))
      hpatch
  have hgetSome : code.get? pc.toNat = some 0x61 := by
    rw [hget, hgetTemplate]
  have hparse : (some (0x61 : UInt8) >>= parseInstr) = some (.Push .PUSH2) := by
    native_decide
  unfold decode
  rw [hgetSome, hparse]
  change some (Operation.Push Operation.POp.PUSH2,
      some (uInt256OfByteArray (code.extract' pc.toNat.succ (pc.toNat.succ + 2)), 2)) =
    some (Operation.Push Operation.POp.PUSH2, some (n, 2))
  rw [hextract, hval]

private theorem uniswapV3PoolBurnNonzeroPatchPreservesJumpDest11303 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨11303⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched11303 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨11303⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnNonzeroPatchPreservesJumpDest11303

private theorem uniswapV3PoolBurnNonzeroPatchPreservesJumpDest19199 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨19199⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched19199 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨19199⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnNonzeroPatchPreservesJumpDest19199

private theorem uniswapV3PoolBurnNonzeroPatchPreservesJumpDest13193 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13193⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched13193 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13193⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnNonzeroPatchPreservesJumpDest13193

private theorem uniswapV3PoolBurnNonzeroPatchPreservesJumpDest13226 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13226⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched13226 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13226⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnNonzeroPatchPreservesJumpDest13226

theorem uniswapV3PoolBurnAfterFeeGlobalsNonzeroToTimestampReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcond :
      UInt256.isZero
        (UInt256.signextend ⟨15⟩
          (UInt256.signextend ⟨15⟩
            (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))) = ⟨0⟩)
    (h : RD code ee g s0 ⟨19189⟩
      (⟨19492⟩ ::
        UInt256.isZero
          (UInt256.signextend ⟨15⟩
            (UInt256.signextend ⟨15⟩
              (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))) ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 58 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨19200⟩
      (UInt256.ofNat ee.header.timestamp :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, h19190⟩ :=
    uniswapV3PoolBurnAfterFeeGlobalsLiquidityDeltaNonzeroFallthrough
      hpatch hcond h (by
        have hlen := hov
        omega)
  have hd19190 : decode code ⟨19190⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19192 : decode code ⟨19192⟩ = some (.Push .PUSH2, some (⟨19199⟩, 2)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19195 : decode code ⟨19195⟩ = some (.Push .PUSH2, some (⟨11303⟩, 2)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19198 : decode code ⟨19198⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19199 : decode code ⟨19199⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd11303 : decode code ⟨11303⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnNonzeroTimestampDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd11304 : decode code ⟨11304⟩ = some (.TIMESTAMP, .none) := by
    rw [uniswapV3PoolBurnNonzeroTimestampDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd11305 : decode code ⟨11305⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnNonzeroTimestampDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd11306 : decode code ⟨11306⟩ = some (.JUMP, .none) := by
    rw [uniswapV3PoolBurnNonzeroTimestampDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have h19198 := evm_run h19190 with [
    raw push1 ⟨0⟩ hd19190 (by evm_ov),
    raw push2 ⟨19199⟩ hd19192 (by evm_ov),
    raw push2 ⟨11303⟩ hd19195 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)]
  have h11303 := h19198.jump hd19198 (uniswapV3PoolBurnJumpDestPatched11303 hpatch)
    (by evm_ov)
  have h11306 := evm_run h11303 with [
    raw jumpdest hd11303 (by evm_ov),
    raw timestamp hd11304 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw swap1 hd11305 (by evm_ov)]
  have h19199 := h11306.jump hd11306 (uniswapV3PoolBurnJumpDestPatched19199 hpatch)
    (by evm_ov)
  exact ⟨_, _, evm_run h19199 with [
    raw jumpdest hd19199 (by evm_ov)]⟩

theorem uniswapV3PoolBurnAfterFeeGlobalsNonzeroTimestampToSlot0LiquidityLoaded
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨19200⟩
      (UInt256.ofNat ee.header.timestamp :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 58 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨19214⟩
      (solcSlotWord σ ee ⟨0⟩ :: solcSlotWord σ ee ⟨4⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ee.header.timestamp :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hd19200 : decode code ⟨19200⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19202 : decode code ⟨19202⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19203 : decode code ⟨19203⟩ = some (.SLOAD, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19204 : decode code ⟨19204⟩ = some (.Push .PUSH1, some (⟨4⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19206 : decode code ⟨19206⟩ = some (.SLOAD, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19207 : decode code ⟨19207⟩ = some (.SWAP3, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19208 : decode code ⟨19208⟩ = some (.SWAP4, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19209 : decode code ⟨19209⟩ = some (.POP, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19210 : decode code ⟨19210⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19211 : decode code ⟨19211⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19212 : decode code ⟨19212⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19213 : decode code ⟨19213⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have h19203 := evm_run h with [
    raw push1 ⟨0⟩ hd19200 (by evm_ov),
    raw dup1 hd19202 (by evm_ov)]
  obtain ⟨_, _, h19204⟩ := h19203.sload hd19203 (by
    have hlen := hov
    simp only [List.length_cons] at hlen ⊢
    omega)
  have h19206 := evm_run h19204 with [
    raw push1 ⟨4⟩ hd19204 (by evm_ov)]
  obtain ⟨_, _, h19207⟩ := h19206.sload hd19206 (by
    have hlen := hov
    simp only [List.length_cons] at hlen ⊢
    omega)
  exact ⟨_, _, evm_run h19207 with [
    raw swap3 hd19207 (by evm_ov),
    raw swap4 hd19208 (by evm_ov),
    raw pop hd19209 (by evm_ov),
    raw swap1 hd19210 (by evm_ov),
    raw swap2 hd19211 (by evm_ov),
    raw dup3 hd19212 (by evm_ov),
    raw swap2 hd19213 (by evm_ov)]⟩

theorem uniswapV3PoolBurnAfterFeeGlobalsNonzeroSlot0LiquidityToObserveSingleEntry
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {ret : UInt256} {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨19214⟩
      (solcSlotWord σ ee ⟨0⟩ :: solcSlotWord σ ee ⟨4⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ee.header.timestamp :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 64 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13193⟩
      (((solcSlotWord σ ee ⟨0⟩).div ((⟨1⟩ : UInt256).shiftLeft ⟨200⟩)).land ⟨65535⟩ ::
        (solcSlotWord σ ee ⟨4⟩).land (((⟨1⟩ : UInt256).shiftLeft ⟨128⟩).sub ⟨1⟩) ::
        (⟨65535⟩ : UInt256).land
          ((solcSlotWord σ ee ⟨0⟩).div ((⟨1⟩ : UInt256).shiftLeft ⟨184⟩)) ::
        (⟨2⟩ : UInt256).signextend
          ((solcSlotWord σ ee ⟨0⟩).div ((⟨1⟩ : UInt256).shiftLeft ⟨160⟩)) ::
        ⟨0⟩ :: UInt256.ofNat ee.header.timestamp :: ⟨8⟩ :: ⟨19273⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: UInt256.ofNat ee.header.timestamp :: ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        burnPositionBaseSlotWord σ ee :: slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hd19214 : decode code ⟨19214⟩ = some (.Push .PUSH2, some (⟨19273⟩, 2)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19217 : decode code ⟨19217⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19218 : decode code ⟨19218⟩ = some (.Push .PUSH1, some (⟨8⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19220 : decode code ⟨19220⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19221 : decode code ⟨19221⟩ = some (.DUP7, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19222 : decode code ⟨19222⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19223 : decode code ⟨19223⟩ = some (.DUP6, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19224 : decode code ⟨19224⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19225 : decode code ⟨19225⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19227 : decode code ⟨19227⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19229 : decode code ⟨19229⟩ = some (.SHL, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19230 : decode code ⟨19230⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19231 : decode code ⟨19231⟩ = some (.DIV, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19232 : decode code ⟨19232⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19234 : decode code ⟨19234⟩ = some (.SIGNEXTEND, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19235 : decode code ⟨19235⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19236 : decode code ⟨19236⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19239 : decode code ⟨19239⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19241 : decode code ⟨19241⟩ = some (.Push .PUSH1, some (⟨184⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19243 : decode code ⟨19243⟩ = some (.SHL, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19244 : decode code ⟨19244⟩ = some (.DUP4, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19245 : decode code ⟨19245⟩ = some (.DIV, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19246 : decode code ⟨19246⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19247 : decode code ⟨19247⟩ = some (.AND, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19248 : decode code ⟨19248⟩ = some (.SWAP3, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19249 : decode code ⟨19249⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19251 : decode code ⟨19251⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19253 : decode code ⟨19253⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19255 : decode code ⟨19255⟩ = some (.SHL, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19256 : decode code ⟨19256⟩ = some (.SUB, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19257 : decode code ⟨19257⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19258 : decode code ⟨19258⟩ = some (.SWAP3, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19259 : decode code ⟨19259⟩ = some (.AND, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19260 : decode code ⟨19260⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19261 : decode code ⟨19261⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [uniswapV3PoolBurnNonzeroStartDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd19263 : decode code ⟨19263⟩ = some (.Push .PUSH1, some (⟨200⟩, 1)) := by
    exact uniswapV3PoolBurnNonzeroDecodePatchedPush1 hpatch (by native_decide)
      (uniswapV3PoolBurnNonzeroShortPatchDisjoint
        (pc := ⟨19263⟩) (n := 2) (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd19265 : decode code ⟨19265⟩ = some (.SHL, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19265⟩) (byte := 0x1b)
      (op := .SHL) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnNonzeroShortPatchDisjoint
      (pc := ⟨19265⟩) (n := 1) (by native_decide) (by native_decide)
  have hd19266 : decode code ⟨19266⟩ = some (.SWAP1, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19266⟩) (byte := 0x90)
      (op := .SWAP1) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnNonzeroShortPatchDisjoint
      (pc := ⟨19266⟩) (n := 1) (by native_decide) (by native_decide)
  have hd19267 : decode code ⟨19267⟩ = some (.DIV, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19267⟩) (byte := 0x04)
      (op := .DIV) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnNonzeroShortPatchDisjoint
      (pc := ⟨19267⟩) (n := 1) (by native_decide) (by native_decide)
  have hd19268 : decode code ⟨19268⟩ = some (.AND, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19268⟩) (byte := 0x16)
      (op := .AND) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnNonzeroShortPatchDisjoint
      (pc := ⟨19268⟩) (n := 1) (by native_decide) (by native_decide)
  have hd19269 : decode code ⟨19269⟩ = some (.Push .PUSH2, some (⟨13193⟩, 2)) := by
    exact uniswapV3PoolBurnNonzeroDecodePatchedPush2 hpatch (by native_decide)
      (uniswapV3PoolBurnNonzeroShortPatchDisjoint
        (pc := ⟨19269⟩) (n := 3) (by native_decide) (by native_decide))
      (by native_decide) (by native_decide)
  have hd19272 : decode code ⟨19272⟩ = some (.JUMP, .none) := by
    refine uniswapV3PoolDecodePatchedNoArg (pc := ⟨19272⟩) (byte := 0x56)
      (op := .JUMP) hpatch (by native_decide) ?_ (by native_decide)
      (by native_decide) (by native_decide)
    exact uniswapV3PoolBurnNonzeroShortPatchDisjoint
      (pc := ⟨19272⟩) (n := 1) (by native_decide) (by native_decide)
  have h19234 := evm_run h with [
    raw push2 ⟨19273⟩ hd19214 (by evm_ov),
    raw swap2 hd19217 (by evm_ov),
    raw push1 ⟨8⟩ hd19218 (by evm_ov),
    raw swap2 hd19220 (by evm_ov),
    raw dup7 hd19221 (by evm_ov),
    raw swap2 hd19222 (by evm_ov),
    raw dup6 hd19223 (by evm_ov),
    raw swap2 hd19224 (by evm_ov),
    raw push1 ⟨1⟩ hd19225 (by evm_ov),
    raw push1 ⟨160⟩ hd19227 (by evm_ov),
    raw shl hd19229 (by evm_ov),
    raw dup2 hd19230 (by evm_ov),
    raw div hd19231 (by evm_ov),
    raw push1 ⟨2⟩ hd19232 (by evm_ov)]
  have h19235 := RD.signextend h19234 hd19234 (by
    have hlen := hov
    simp only [List.length_cons] at hlen ⊢
    omega)
  have h19272 := evm_run h19235 with [
    raw swap2 hd19235 (by evm_ov),
    raw push2 ⟨65535⟩ hd19236 (by evm_ov),
    raw push1 ⟨1⟩ hd19239 (by evm_ov),
    raw push1 ⟨184⟩ hd19241 (by evm_ov),
    raw shl hd19243 (by evm_ov),
    raw dup4 hd19244 (by evm_ov),
    raw div hd19245 (by evm_ov),
    raw dup2 hd19246 (by evm_ov),
    raw and hd19247 (by evm_ov),
    raw swap3 hd19248 (by evm_ov),
    raw push1 ⟨1⟩ hd19249 (by evm_ov),
    raw push1 ⟨1⟩ hd19251 (by evm_ov),
    raw push1 ⟨128⟩ hd19253 (by evm_ov),
    raw shl hd19255 (by evm_ov),
    raw sub hd19256 (by evm_ov),
    raw swap1 hd19257 (by evm_ov),
    raw swap3 hd19258 (by evm_ov),
    raw and hd19259 (by evm_ov),
    raw swap2 hd19260 (by evm_ov),
    raw push1 ⟨1⟩ hd19261 (by evm_ov),
    raw push1 ⟨200⟩ hd19263 (by evm_ov),
    raw shl hd19265 (by evm_ov),
    raw swap1 hd19266 (by evm_ov),
    raw div hd19267 (by evm_ov),
    raw and hd19268 (by evm_ov),
    raw push2 ⟨13193⟩ hd19269 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)]
  exact ⟨_, _, h19272.jump hd19272 (uniswapV3PoolBurnJumpDestPatched13193 hpatch)
    (by evm_ov)⟩

theorem uniswapV3PoolBurnObserveSingleSecondsAgoZeroFallthrough
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cardinality liquidity index tick time memPtr ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13193⟩
      (cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time :: memPtr :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13208⟩
      (⟨0⟩ :: ⟨0⟩ ::
        cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time :: memPtr :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hd13193 : decode code ⟨13193⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13194 : decode code ⟨13194⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13196 : decode code ⟨13196⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13197 :
      decode code ⟨13197⟩ = some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13202 : decode code ⟨13202⟩ = some (.DUP8, .none) := by
    rw [uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13203 : decode code ⟨13203⟩ = some (.AND, .none) := by
    rw [uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13204 : decode code ⟨13204⟩ = some (.Push .PUSH2, some (⟨13360⟩, 2)) := by
    rw [uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13207 : decode code ⟨13207⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnObserveSingleZeroDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have h13194 := h.jumpdest hd13193 (by
    have hlen := hov
    simp only [List.length_cons] at hlen ⊢
    omega)
  have h13207 := evm_run h13194 with [
    raw push1 ⟨0⟩ hd13194 (by evm_ov),
    raw dup1 hd13196 (by evm_ov),
    raw push4 ⟨4294967295⟩ hd13197 (by evm_ov),
    raw dup8 hd13202 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw and hd13203 (by evm_ov),
    raw push2 ⟨13360⟩ hd13204 (by evm_ov)]
  exact ⟨_, _, h13207.jumpiNT hd13207 (by native_decide) (by
    have hlen := hov
    simp only [List.length_cons] at hlen ⊢
    omega)⟩

theorem burnRDInvalidError {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {pc : UInt256} {stk : List UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (h : RD code ee g s0 pc stk mem aw rdata acc k C)
    (hdec : decode code pc = some (.INVALID, .none)) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction := by
  rcases RD.conclude h with hoog | ⟨k', C', s', hX, hcode, hpc, _hstk, _hgas, hk, hC,
    _hmem, _haw, _hrdata, _hacc⟩
  · exact Or.inl hoog
  · have hdec' : decode s'.executionEnv.code s'.machineState.pc = some (.INVALID, .none) := by
      rw [hcode, hpc]
      exact hdec
    have hstep : Xstep (D_J code 0) s' = .error .InvalidInstruction := by
      have hstep' := Ethereum.EVM.step_invalid s' hdec'
      simpa [hcode] using hstep'
    have hfuel : g.toNat + 1 - k' = (g.toNat + 1 - (k' + 1)) + 1 := by
      omega
    exact Or.inr (by
      rw [hX, hfuel]
      exact Ethereum.EVM.Xstep_X_X_except _ s' _ _ hstep)

theorem uniswapV3PoolBurnObserveSingleIndexOobInvalid
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cardinality liquidity index tick time memPtr ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13208⟩
      (⟨0⟩ :: ⟨0⟩ :: cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time ::
        memPtr :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hlt : UInt256.lt ((⟨65535⟩ : UInt256).land index) ⟨65535⟩ = ⟨0⟩)
    (hov : R.length + 15 ≤ 1024) :
    X (g.toNat + 1) (D_J code 0) s0 = .error .OutOfGass ∨
      X (g.toNat + 1) (D_J code 0) s0 = .error .InvalidInstruction := by
  have hd13208 : decode code ⟨13208⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13210 : decode code ⟨13210⟩ = some (.DUP10, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13211 : decode code ⟨13211⟩ = some (.DUP7, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13212 : decode code ⟨13212⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13215 : decode code ⟨13215⟩ = some (.AND, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13216 : decode code ⟨13216⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13219 : decode code ⟨13219⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13220 : decode code ⟨13220⟩ = some (.LT, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13221 : decode code ⟨13221⟩ = some (.Push .PUSH2, some (⟨13226⟩, 2)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13224 : decode code ⟨13224⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13225 : decode code ⟨13225⟩ = some (.INVALID, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have h13221 := evm_run h with [
    raw push1 ⟨0⟩ hd13208 (by evm_ov),
    raw dup10 hd13210 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw dup7 hd13211 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw push2 ⟨65535⟩ hd13212 (by evm_ov),
    raw and hd13215 (by evm_ov),
    raw push2 ⟨65535⟩ hd13216 (by evm_ov),
    raw dup2 hd13219 (by evm_ov),
    raw lt hd13220 (by evm_ov)]
  rw [hlt] at h13221
  have h13224 := evm_run h13221 with [
    raw push2 ⟨13226⟩ hd13221 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)]
  have h13225 := h13224.jumpiNT hd13224 (by native_decide) (by
    have hlen := hov
    simp only [List.length_cons] at hlen ⊢
    omega)
  exact burnRDInvalidError h13225 hd13225

theorem uniswapV3PoolBurnObserveSingleIndexInBoundsJump
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cardinality liquidity index tick time memPtr ret : UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13208⟩
      (⟨0⟩ :: ⟨0⟩ :: cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time ::
        memPtr :: ret :: R)
      mem aw rdata (cA, σ) k C)
    (hlt : UInt256.lt ((⟨65535⟩ : UInt256).land index) ⟨65535⟩ ≠ ⟨0⟩)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13226⟩
      (((⟨65535⟩ : UInt256).land index) :: memPtr :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time :: memPtr :: ret :: R)
      mem aw rdata (cA, σ) k' C' := by
  have hd13208 : decode code ⟨13208⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13210 : decode code ⟨13210⟩ = some (.DUP10, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13211 : decode code ⟨13211⟩ = some (.DUP7, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13212 : decode code ⟨13212⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13215 : decode code ⟨13215⟩ = some (.AND, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13216 : decode code ⟨13216⟩ = some (.Push .PUSH2, some (⟨65535⟩, 2)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13219 : decode code ⟨13219⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13220 : decode code ⟨13220⟩ = some (.LT, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13221 : decode code ⟨13221⟩ = some (.Push .PUSH2, some (⟨13226⟩, 2)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13224 : decode code ⟨13224⟩ = some (.JUMPI, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have h13221 := evm_run h with [
    raw push1 ⟨0⟩ hd13208 (by evm_ov),
    raw dup10 hd13210 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw dup7 hd13211 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw push2 ⟨65535⟩ hd13212 (by evm_ov),
    raw and hd13215 (by evm_ov),
    raw push2 ⟨65535⟩ hd13216 (by evm_ov),
    raw dup2 hd13219 (by evm_ov),
    raw lt hd13220 (by evm_ov)]
  have h13224 := evm_run h13221 with [
    raw push2 ⟨13226⟩ hd13221 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)]
  exact ⟨_, _, h13224.jumpiT hd13224 hlt
    (uniswapV3PoolBurnJumpDestPatched13226 hpatch) (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)⟩

noncomputable abbrev burnObserveSingleAllocMem (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnPositionKeyMappingMem σ I) 64
    (burnPositionKeyNewFreePtrWord + (⟨128⟩ : UInt256))

theorem burnPositionKeyMappingMem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnPositionKeyMappingMem σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnPositionKeyMappingMem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      burnPositionKeyNewFreePtrWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionKeyMappingMem σ I) (aw := UInt256.ofNat 18)
    (off := ⟨64⟩) (v := burnPositionKeyNewFreePtrWord)
    (by rw [burnPositionKeyMappingMem_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnPositionKeyMappingMem_read64 σ I)

theorem uniswapV3PoolBurnObserveSingleLoadObservation
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {cardinality liquidity index tick time ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13226⟩
      (((⟨65535⟩ : UInt256).land index) :: ⟨8⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time :: ⟨8⟩ :: ret :: R)
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 17 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13242⟩
      (solcSlotWord σ ee (⟨8⟩ + ((⟨65535⟩ : UInt256).land index)) ::
        burnPositionKeyNewFreePtrWord :: ⟨64⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time :: ⟨8⟩ :: ret :: R)
      (burnObserveSingleAllocMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hd13226 : decode code ⟨13226⟩ = some (.JUMPDEST, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13227 : decode code ⟨13227⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13229 : decode code ⟨13229⟩ = some (.DUP1, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13230 : decode code ⟨13230⟩ = some (.MLOAD, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13231 : decode code ⟨13231⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13233 : decode code ⟨13233⟩ = some (.DUP2, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13234 : decode code ⟨13234⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13235 : decode code ⟨13235⟩ = some (.DUP3, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13236 : decode code ⟨13236⟩ = some (.MSTORE, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13237 : decode code ⟨13237⟩ = some (.SWAP2, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13238 : decode code ⟨13238⟩ = some (.SWAP1, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13239 : decode code ⟨13239⟩ = some (.SWAP3, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13240 : decode code ⟨13240⟩ = some (.ADD, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have hd13241 : decode code ⟨13241⟩ = some (.SLOAD, .none) := by
    rw [uniswapV3PoolBurnObserveSingleBoundDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)]
    native_decide
  have h13230 := evm_run h with [
    raw jumpdest hd13226 (by evm_ov),
    raw push1 ⟨64⟩ hd13227 (by evm_ov),
    raw dup1 hd13229 (by evm_ov)]
  have h13231 := by
    simpa using
      h13230.mload 0 burnPositionKeyNewFreePtrWord (UInt256.ofNat 18)
        hd13230 mem_cost (burnPositionKeyMappingMem_mload64 σ ee)
        (by native_decide)
        (by
          have hlen := hov
          simp only [List.length_cons] at hlen ⊢
          omega)
  have h13237 := evm_run h13231 with [
    raw push1 ⟨128⟩ hd13231 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw dup2 hd13233 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw add hd13234 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw dup3 hd13235 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw mstore 0 (burnObserveSingleAllocMem σ ee) (UInt256.ofNat 18)
      hd13236 mem_cost rfl (by native_decide) (by
        have hlen := hov
        simp only [List.length_cons] at hlen ⊢
        omega),
    raw swap2 hd13237 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw swap1 hd13238 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw swap3 hd13239 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw add hd13240 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)]
  obtain ⟨_, _, h13242⟩ := h13237.sload hd13241 (by
    have hlen := hov
    simp only [List.length_cons] at hlen ⊢
    omega)
  exact ⟨_, _, by simpa [solcSlotWord, u256_add_comm] using h13242⟩

end Benchmarks.UniswapV3Pool
