import Benchmarks.UniswapV3Pool.BurnTickGetFeeGrowthInsideSource
import Benchmarks.UniswapV3Pool.BurnPostPositionUpdate

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev burnModifyPositionAfterPositionUpdateFrame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnModifyPositionAfterFeeGrowthInsideFrame v σ I).locals.insert
      "_positionUpdated" .unit }

abbrev burnModifyPositionAfterAmount0Frame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnModifyPositionAfterPositionUpdateFrame v σ I).locals.insert
      "amount0" (.int 0) }

abbrev burnModifyPositionAfterAmount1Frame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnModifyPositionAfterAmount0Frame v σ I).locals.insert
      "amount1" (.int 0) }

theorem burnAfterPositionUpdateFrame_liquidityDelta {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterPositionUpdateFrame v σ I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionAfterPositionUpdateFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthInsideFrame v σ I).locals
    (k := "_positionUpdated") (a := "liquidityDelta") .unit (by native_decide)]
  exact burnAfterFeeGrowthInsideFrame_liquidityDelta σ I

theorem burnAfterPositionUpdateFrame_positionKey {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterPositionUpdateFrame v σ I).locals.get? "_positionKey" =
      some (burnPositionKeyValue I) := by
  rw [burnModifyPositionAfterPositionUpdateFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthInsideFrame v σ I).locals
    (k := "_positionUpdated") (a := "_positionKey") .unit (by native_decide)]
  exact burnAfterFeeGrowthInsideFrame_positionKey σ I

theorem burnAfterAmount0Frame_liquidityDelta {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterAmount0Frame v σ I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionAfterAmount0Frame]
  rw [store_get_ne (burnModifyPositionAfterPositionUpdateFrame v σ I).locals
    (k := "amount0") (a := "liquidityDelta") (.int 0) (by native_decide)]
  exact burnAfterPositionUpdateFrame_liquidityDelta σ I

theorem burnAfterAmount1Frame_liquidityDelta {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterAmount1Frame v σ I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionAfterAmount1Frame]
  rw [store_get_ne (burnModifyPositionAfterAmount0Frame v σ I).locals
    (k := "amount1") (a := "liquidityDelta") (.int 0) (by native_decide)]
  exact burnAfterAmount0Frame_liquidityDelta σ I

theorem burnAfterAmount1Frame_positionKey {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterAmount1Frame v σ I).locals.get? "_positionKey" =
      some (burnPositionKeyValue I) := by
  rw [burnModifyPositionAfterAmount1Frame, burnModifyPositionAfterAmount0Frame]
  rw [store_get_ne (burnModifyPositionAfterAmount0Frame v σ I).locals
    (k := "amount1") (a := "_positionKey") (.int 0) (by native_decide)]
  rw [store_get_ne (burnModifyPositionAfterPositionUpdateFrame v σ I).locals
    (k := "amount0") (a := "_positionKey") (.int 0) (by native_decide)]
  exact burnAfterPositionUpdateFrame_positionKey σ I

theorem burnAfterAmount1Frame_amount0 {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterAmount1Frame v σ I).locals.get? "amount0" =
      some (.int 0) := by
  rw [burnModifyPositionAfterAmount1Frame]
  rw [store_get_ne (burnModifyPositionAfterAmount0Frame v σ I).locals
    (k := "amount1") (a := "amount0") (.int 0) (by native_decide)]
  rw [burnModifyPositionAfterAmount0Frame]
  exact store_get_self (burnModifyPositionAfterPositionUpdateFrame v σ I).locals
    "amount0" (.int 0)

theorem burnAfterAmount1Frame_amount1 {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterAmount1Frame v σ I).locals.get? "amount1" =
      some (.int 0) := by
  rw [burnModifyPositionAfterAmount1Frame]
  exact store_get_self (burnModifyPositionAfterAmount0Frame v σ I).locals "amount1" (.int 0)

theorem burnModifyPosition_evalLiquidityDeltaLtZeroFalseAfterPositionUpdate
    {v : PoolImmutables} {evm σ I}
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    evalExpr? (config v) (burnModifyPositionAfterPositionUpdateFrame v σ I) evm
      (ltE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool false) := by
  simp only [ltE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnAfterPositionUpdateFrame_liquidityDelta (v := v) (σ := σ) (I := I)]
  simp [EvalResult.ofOption, burnLiquidityDeltaValue, hzero, evalBinaryOp?]

theorem burnModifyPosition_evalLiquidityDeltaNeZeroFalseAfterAmount1
    {v : PoolImmutables} {evm σ I}
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    evalExpr? (config v) (burnModifyPositionAfterAmount1Frame v σ I) evm
      (neE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool false) := by
  simp only [neE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnAfterAmount1Frame_liquidityDelta (v := v) (σ := σ) (I := I)]
  simp [EvalResult.ofOption, burnLiquidityDeltaValue, hzero, evalBinaryOp?]

theorem burnModifyPosition_evalReturnValuesAfterAmount1 {v : PoolImmutables}
    {evm σ I} :
    evalExprs? (config v) (burnModifyPositionAfterAmount1Frame v σ I) evm
      [.var "_positionKey", .var "amount0", .var "amount1"] =
        .ok [burnPositionKeyValue I, .int 0, .int 0] := by
  simp only [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnAfterAmount1Frame_positionKey (v := v) (σ := σ) (I := I)]
  rw [burnAfterAmount1Frame_amount0 (v := v) (σ := σ) (I := I)]
  rw [burnAfterAmount1Frame_amount1 (v := v) (σ := σ) (I := I)]
  rfl

abbrev burnModifyPositionAfterPositionUpdateTail : List Stmt :=
  [ Stmt.ite (ltE (.var "liquidityDelta") (.intLit 0))
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
              [ .var "sqrtRatioLowerBelow", .var "sqrtRatioUpperBelow", .var "liquidityDelta" ]
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

theorem uniswapV3PoolModifyPositionSourceZeroDeltaAfterPositionUpdateTail
    {v : PoolImmutables} {evm σ I}
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    ExecBlock (config v) (burnModifyPositionAfterPositionUpdateFrame v σ I) evm
      [ Stmt.ite (ltE (.var "liquidityDelta") (.intLit 0))
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
      (.returned (burnModifyPositionAfterAmount1Frame v σ I) evm
        (some [burnPositionKeyValue I, .int 0, .int 0])) := by
  have hskipClears :
      ExecStmt (config v) (burnModifyPositionAfterPositionUpdateFrame v σ I) evm
        (Stmt.ite (ltE (.var "liquidityDelta") (.intLit 0))
          [ Stmt.ite (.var "flippedLower")
              [ .internalCall "tickClear" [.var "tickLower"] "_clearLower" ]
              [],
            Stmt.ite (.var "flippedUpper")
              [ .internalCall "tickClear" [.var "tickUpper"] "_clearUpper" ]
              [] ]
          [])
        (.ok (burnModifyPositionAfterPositionUpdateFrame v σ I) evm) := by
    refine ExecStmt.iteFalse
      (burnModifyPosition_evalLiquidityDeltaLtZeroFalseAfterPositionUpdate
        (v := v) (evm := evm) (σ := σ) (I := I) hzero) ?_
    exact ExecBlock.nil
  have hamount0 :
      ExecStmt (config v) (burnModifyPositionAfterPositionUpdateFrame v σ I) evm
        (.letDecl "amount0" (some int256) (.intLit 0))
        (.ok (burnModifyPositionAfterAmount0Frame v σ I) evm) := by
    refine ExecStmt.letDecl ?_
    simp [evalExpr?, pure]
  have hamount1 :
      ExecStmt (config v) (burnModifyPositionAfterAmount0Frame v σ I) evm
        (.letDecl "amount1" (some int256) (.intLit 0))
        (.ok (burnModifyPositionAfterAmount1Frame v σ I) evm) := by
    refine ExecStmt.letDecl ?_
    simp [evalExpr?, pure]
  have hskipAmounts :
      ExecStmt (config v) (burnModifyPositionAfterAmount1Frame v σ I) evm
        (Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
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
          [])
        (.ok (burnModifyPositionAfterAmount1Frame v σ I) evm) := by
    refine ExecStmt.iteFalse
      (burnModifyPosition_evalLiquidityDeltaNeZeroFalseAfterAmount1
        (v := v) (evm := evm) (σ := σ) (I := I) hzero) ?_
    exact ExecBlock.nil
  have hret :
      ExecStmt (config v) (burnModifyPositionAfterAmount1Frame v σ I) evm
        (.return [.var "_positionKey", .var "amount0", .var "amount1"])
        (.returned (burnModifyPositionAfterAmount1Frame v σ I) evm
          (some [burnPositionKeyValue I, .int 0, .int 0])) := by
    refine ExecStmt.return ?_
    exact burnModifyPosition_evalReturnValuesAfterAmount1 (v := v) (evm := evm)
      (σ := σ) (I := I)
  exact ExecBlock.consNormal hskipClears <|
    ExecBlock.consNormal hamount0 <|
      ExecBlock.consNormal hamount1 <|
        ExecBlock.consNormal hskipAmounts <|
          ExecBlock.consReturn hret

theorem uniswapV3PoolModifyPositionSourceZeroDeltaAfterPositionUpdateTailNamed
    {v : PoolImmutables} {evm σ I}
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    ExecBlock (config v) (burnModifyPositionAfterPositionUpdateFrame v σ I) evm
      burnModifyPositionAfterPositionUpdateTail
      (.returned (burnModifyPositionAfterAmount1Frame v σ I) evm
        (some [burnPositionKeyValue I, .int 0, .int 0])) := by
  simpa [burnModifyPositionAfterPositionUpdateTail] using
    uniswapV3PoolModifyPositionSourceZeroDeltaAfterPositionUpdateTail
      (v := v) (evm := evm) (σ := σ) (I := I) hzero

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedZeroReturnsValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (htokens0 :
      burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat) = 0)
    (htokens1 :
      burnPositionUpdateSourceTokensOwed1Int σ I
          (Int.ofNat feeGrowthInside1X128.toNat) = 0) :
    ExecFuncBody (config v)
      (burnPositionUpdateValueFrame v I (.int (Int.ofNat feeGrowthInside0X128.toNat))
        (.int (Int.ofNat feeGrowthInside1X128.toNat)))
      (initState cA gh bl σ σ₀ g A I) positionUpdateFunction.body
      (.returned
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [positionUpdateFunction] using
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedZeroBlockValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
      hzero hliq htokens0 htokens1

theorem uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedTrueReturnsValue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (hcond :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)
        (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true)) :
    ExecFuncBody (config v)
      (burnPositionUpdateValueFrame v I (.int (Int.ofNat feeGrowthInside0X128.toNat))
        (.int (Int.ofNat feeGrowthInside1X128.toNat)))
      (initState cA gh bl σ σ₀ g A I) positionUpdateFunction.body
      (.returned
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (burnPositionUpdateSourceAfterTokensOwedState
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
              (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
            I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
            feeGrowthInside1X128)
          σ I feeGrowthInside0X128 feeGrowthInside1X128)
        none) := by
  refine ExecFuncBody.execBlockOK ?_
  simpa [positionUpdateFunction] using
    uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedTrueBlockValue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
      hzero hliq hcond

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolModifyPositionSourceZeroDeltaTailReturnsZeroTokens
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hinside0 :
      burnTickGetInside0Value σ I = .int (Int.ofNat feeGrowthInside0X128.toNat))
    (hinside1 :
      burnTickGetInside1Value σ I = .int (Int.ofNat feeGrowthInside1X128.toNat))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (htokens0 :
      burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat) = 0)
    (htokens1 :
      burnPositionUpdateSourceTokensOwed1Int σ I
          (Int.ofNat feeGrowthInside1X128.toNat) = 0) :
    ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (burnModifyPositionAfterLiquidityDeltaTail v)
      (.returned (burnModifyPositionAfterAmount1Frame v σ I)
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)
        (some [burnPositionKeyValue I, .int 0, .int 0])) := by
  let evmFees :=
    Solm.EVM.storageStore
      (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
        (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
      I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
      feeGrowthInside1X128
  change ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
    (initState cA gh bl σ σ₀ g A I)
    ([ .internalCall "tickGetFeeGrowthInside"
        [ .var "tickLower", .var "tickUpper", .var "_slot0tick",
          .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128" ]
        "feeGrowthInside",
      .internalCall "positionUpdate"
        [ .var "_positionKey", .var "liquidityDelta", tuple0 (.var "feeGrowthInside"),
          tuple1 (.var "feeGrowthInside") ]
        "_positionUpdated" ] ++ burnModifyPositionAfterPositionUpdateTail)
    (.returned (burnModifyPositionAfterAmount1Frame v σ I) evmFees
      (some [burnPositionKeyValue I, .int 0, .int 0]))
  refine ExecBlock.consNormal
    (solm' := burnModifyPositionAfterFeeGrowthInsideFrame v σ I)
    (evm' := initState cA gh bl σ σ₀ g A I) ?_ ?_
  · have hstmt := internalCallFunctionReturn (callee := tickGetFeeGrowthInsideFunction)
      (retVar := "feeGrowthInside")
      (argVals := burnTickGetFeeGrowthInsideArgValues σ I)
      (locals := burnTickGetFeeGrowthInsideStore σ I)
      (calleeSolm := burnTickGetAfterAbove1Frame v σ I)
      (value := some [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I])
      (burnModifyPosition_evalTickGetFeeGrowthInsideArgs (v := v) (cA := cA)
        (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
      (by
        simpa [burnModifyPositionAfterFeeGrowthGlobalsFrame] using
          uniswapV3PoolLookupTickGetFeeGrowthInside v)
      (burnTickGetFeeGrowthInside_bindParams σ I)
      (uniswapV3PoolTickGetFeeGrowthInsideSourceReturns (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g))
    simpa [burnModifyPositionAfterFeeGrowthInsideFrame, resumeAfterInternalCall,
      collapseReturns] using hstmt
  · refine ExecBlock.consNormal
      (solm' := burnModifyPositionAfterPositionUpdateFrame v σ I)
      (evm' := evmFees) ?_ ?_
    · have hbody :=
        uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedZeroReturnsValue
          (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
          hzero hliq htokens0 htokens1
      change ExecFuncBody (config v)
        (burnPositionUpdateValueFrame v I (.int (Int.ofNat feeGrowthInside0X128.toNat))
          (.int (Int.ofNat feeGrowthInside1X128.toNat)))
        (initState cA gh bl σ σ₀ g A I) positionUpdateFunction.body
        (.returned
          (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
            (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
          evmFees none) at hbody
      have hstmt := internalCallFunctionReturn (callee := positionUpdateFunction)
        (retVar := "_positionUpdated")
        (argVals := burnPositionUpdateValueArgValues I
          (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I))
        (locals := burnPositionUpdateValueStore I
          (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I))
        (calleeSolm := burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (value := none)
        (burnModifyPosition_evalPositionUpdateArgsAfterFeeGrowthInside
          (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g))
        (by
          simpa [burnModifyPositionAfterFeeGrowthInsideFrame] using
            uniswapV3PoolLookupPositionUpdate v)
        (by
          simpa [hinside0, hinside1] using
            burnPositionUpdateValue_bindParams I
              (.int (Int.ofNat feeGrowthInside0X128.toNat))
              (.int (Int.ofNat feeGrowthInside1X128.toNat)))
        (by
          simpa [hinside0, hinside1, burnPositionUpdateValueFrame] using hbody)
      simpa [burnModifyPositionAfterPositionUpdateFrame, resumeAfterInternalCall,
        collapseReturns] using hstmt
    · exact uniswapV3PoolModifyPositionSourceZeroDeltaAfterPositionUpdateTailNamed
        (v := v) (evm := evmFees) (σ := σ) (I := I) hzero

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolModifyPositionSourceZeroDeltaReturnsZeroTokens
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hinside0 :
      burnTickGetInside0Value σ I = .int (Int.ofNat feeGrowthInside0X128.toNat))
    (hinside1 :
      burnTickGetInside1Value σ I = .int (Int.ofNat feeGrowthInside1X128.toNat))
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (htokens0 :
      burnPositionUpdateSourceTokensOwed0Int σ I
          (Int.ofNat feeGrowthInside0X128.toNat) = 0)
    (htokens1 :
      burnPositionUpdateSourceTokensOwed1Int σ I
          (Int.ofNat feeGrowthInside1X128.toNat) = 0) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body
      (.returned (burnModifyPositionAfterAmount1Frame v σ I)
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)
        (some [burnPositionKeyValue I, .int 0, .int 0])) := by
  refine ExecFuncBody.execBlockRet ?_
  have hprefix := uniswapV3PoolModifyPositionSourceThroughLiquidityDeltaZeroSkip
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hguard htickLt hge hle hzero
  have htail := uniswapV3PoolModifyPositionSourceZeroDeltaTailReturnsZeroTokens
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
    hinside0 hinside1 hzero hliq htokens0 htokens1
  simpa [modifyPositionFunction, burnModifyPositionSlot0Prefix,
    burnModifyPositionPositionKeyStep, burnModifyPositionFeeGrowthGlobalsStep,
    burnModifyPositionLiquidityDeltaUpdateStep, burnModifyPositionAfterLiquidityDeltaTail]
    using execBlock_append hprefix htail

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolModifyPositionSourceZeroDeltaTailReturnsTokensOwed
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hinside0 :
      burnTickGetInside0Value σ I = .int (Int.ofNat feeGrowthInside0X128.toNat))
    (hinside1 :
      burnTickGetInside1Value σ I = .int (Int.ofNat feeGrowthInside1X128.toNat))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (hcond :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)
        (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true)) :
    ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (burnModifyPositionAfterLiquidityDeltaTail v)
      (.returned (burnModifyPositionAfterAmount1Frame v σ I)
        (burnPositionUpdateSourceAfterTokensOwedState
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
              (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
            I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
            feeGrowthInside1X128)
          σ I feeGrowthInside0X128 feeGrowthInside1X128)
        (some [burnPositionKeyValue I, .int 0, .int 0])) := by
  let evmFees :=
    Solm.EVM.storageStore
      (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
        (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
      I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1X128
  let evmTokens :=
    burnPositionUpdateSourceAfterTokensOwedState evmFees σ I
      feeGrowthInside0X128 feeGrowthInside1X128
  change ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
    (initState cA gh bl σ σ₀ g A I)
    ([ .internalCall "tickGetFeeGrowthInside"
        [ .var "tickLower", .var "tickUpper", .var "_slot0tick",
          .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128" ]
        "feeGrowthInside",
      .internalCall "positionUpdate"
        [ .var "_positionKey", .var "liquidityDelta", tuple0 (.var "feeGrowthInside"),
          tuple1 (.var "feeGrowthInside") ]
        "_positionUpdated" ] ++ burnModifyPositionAfterPositionUpdateTail)
    (.returned (burnModifyPositionAfterAmount1Frame v σ I) evmTokens
      (some [burnPositionKeyValue I, .int 0, .int 0]))
  refine ExecBlock.consNormal
    (solm' := burnModifyPositionAfterFeeGrowthInsideFrame v σ I)
    (evm' := initState cA gh bl σ σ₀ g A I) ?_ ?_
  · have hstmt := internalCallFunctionReturn (callee := tickGetFeeGrowthInsideFunction)
      (retVar := "feeGrowthInside")
      (argVals := burnTickGetFeeGrowthInsideArgValues σ I)
      (locals := burnTickGetFeeGrowthInsideStore σ I)
      (calleeSolm := burnTickGetAfterAbove1Frame v σ I)
      (value := some [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I])
      (burnModifyPosition_evalTickGetFeeGrowthInsideArgs (v := v) (cA := cA)
        (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
      (by
        simpa [burnModifyPositionAfterFeeGrowthGlobalsFrame] using
          uniswapV3PoolLookupTickGetFeeGrowthInside v)
      (burnTickGetFeeGrowthInside_bindParams σ I)
      (uniswapV3PoolTickGetFeeGrowthInsideSourceReturns (v := v)
        (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
        (I := I) (g := g))
    simpa [burnModifyPositionAfterFeeGrowthInsideFrame, resumeAfterInternalCall,
      collapseReturns] using hstmt
  · refine ExecBlock.consNormal
      (solm' := burnModifyPositionAfterPositionUpdateFrame v σ I)
      (evm' := evmTokens) ?_ ?_
    · have hbody :=
        uniswapV3PoolPositionUpdateSourceZeroDeltaLiquidityNonzeroTokensOwedTrueReturnsValue
          (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
          hzero hliq hcond
      change ExecFuncBody (config v)
        (burnPositionUpdateValueFrame v I (.int (Int.ofNat feeGrowthInside0X128.toNat))
          (.int (Int.ofNat feeGrowthInside1X128.toNat)))
        (initState cA gh bl σ σ₀ g A I) positionUpdateFunction.body
        (.returned
          (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
            (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
          evmTokens none) at hbody
      have hstmt := internalCallFunctionReturn (callee := positionUpdateFunction)
        (retVar := "_positionUpdated")
        (argVals := burnPositionUpdateValueArgValues I
          (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I))
        (locals := burnPositionUpdateValueStore I
          (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I))
        (calleeSolm := burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (value := none)
        (burnModifyPosition_evalPositionUpdateArgsAfterFeeGrowthInside
          (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
          (σ₀ := σ₀) (A := A) (I := I) (g := g))
        (by
          simpa [burnModifyPositionAfterFeeGrowthInsideFrame] using
            uniswapV3PoolLookupPositionUpdate v)
        (by
          simpa [hinside0, hinside1] using
            burnPositionUpdateValue_bindParams I
              (.int (Int.ofNat feeGrowthInside0X128.toNat))
              (.int (Int.ofNat feeGrowthInside1X128.toNat)))
        (by
          simpa [hinside0, hinside1, burnPositionUpdateValueFrame, evmTokens] using hbody)
      simpa [burnModifyPositionAfterPositionUpdateFrame, resumeAfterInternalCall,
        collapseReturns] using hstmt
    · exact uniswapV3PoolModifyPositionSourceZeroDeltaAfterPositionUpdateTailNamed
        (v := v) (evm := evmTokens) (σ := σ) (I := I) hzero

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolModifyPositionSourceZeroDeltaReturnsTokensOwed
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hinside0 :
      burnTickGetInside0Value σ I = .int (Int.ofNat feeGrowthInside0X128.toNat))
    (hinside1 :
      burnTickGetInside1Value σ I = .int (Int.ofNat feeGrowthInside1X128.toNat))
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (hcond :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v σ I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
            (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)
        (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true)) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body
      (.returned (burnModifyPositionAfterAmount1Frame v σ I)
        (burnPositionUpdateSourceAfterTokensOwedState
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner
              (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
            I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
            feeGrowthInside1X128)
          σ I feeGrowthInside0X128 feeGrowthInside1X128)
        (some [burnPositionKeyValue I, .int 0, .int 0])) := by
  refine ExecFuncBody.execBlockRet ?_
  have hprefix := uniswapV3PoolModifyPositionSourceThroughLiquidityDeltaZeroSkip
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hguard htickLt hge hle hzero
  have htail := uniswapV3PoolModifyPositionSourceZeroDeltaTailReturnsTokensOwed
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
    hinside0 hinside1 hzero hliq hcond
  simpa [modifyPositionFunction, burnModifyPositionSlot0Prefix,
    burnModifyPositionPositionKeyStep, burnModifyPositionFeeGrowthGlobalsStep,
    burnModifyPositionLiquidityDeltaUpdateStep, burnModifyPositionAfterLiquidityDeltaTail]
    using execBlock_append hprefix htail

abbrev burnPublicAfterModifiedFrame
    (v : PoolImmutables) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnLiquidityDeltaFrame v I).locals.insert "modified"
      (.tuple [burnPositionKeyValue I, .int 0, .int 0]) }

abbrev burnPublicAfterPositionFrame
    (v : PoolImmutables) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnPublicAfterModifiedFrame v I).locals.insert "position"
      (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) }

abbrev burnPublicAfterAmount0Frame
    (v : PoolImmutables) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnPublicAfterPositionFrame v I).locals.insert "amount0" (.int 0) }

abbrev burnPublicAfterAmount1Frame
    (v : PoolImmutables) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnPublicAfterAmount0Frame v I).locals.insert "amount1" (.int 0) }

theorem burnPositionKeyValue_valueToKey (I : ExecutionEnv) :
    valueToKey? (burnPositionKeyValue I) =
      some (.fixedBytes bytes32Width (ffi.KEC (burnPositionKeyPackedBytes I)).toList) := by
  have hlen :
      (ffi.KEC (burnPositionKeyPackedBytes I)).toList.length = (31 : Nat) + 1 := by
    rw [byteArray_toList_eq, Array.length_toList]
    change (ffi.KEC (burnPositionKeyPackedBytes I)).size = (31 : Nat) + 1
    rw [keccak_size]
  change valueToKey? (burnPositionKeyValue I) =
      some (.fixedBytes (⟨31, by decide⟩ : Fin 32)
        (ffi.KEC (burnPositionKeyPackedBytes I)).toList)
  simp [valueToKey?, hlen]

theorem burnPublicAfterModified_positions {v : PoolImmutables} (I : ExecutionEnv) :
    (burnPublicAfterModifiedFrame v I).locals.get? "positions" = none := by
  rw [burnPublicAfterModifiedFrame, burnLiquidityDeltaFrame, burnStore]
  rw [store_get_ne5 (∅ : Store)
    (k1 := "tickLower") (k2 := "tickUpper") (k3 := "amount")
    (k4 := "liquidityDelta") (k5 := "modified") (a := "positions")
    (burnTickLowerValue I) (burnTickUpperValue I) (burnAmountValue I)
    (burnLiquidityDeltaValue I) (.tuple [burnPositionKeyValue I, .int 0, .int 0])
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)]
  simp

set_option maxHeartbeats 1000000 in
theorem burnPublicAfterModified_evalStorageRef_positions {v : PoolImmutables}
    (evm : EVM.State) (I : ExecutionEnv) :
    evalStorageRef (config v) (burnPublicAfterModifiedFrame v I) evm
      (positionsRef (tuple0 (.var "modified"))) =
        .ok (burnPositionUpdateEvaledBaseRef I) := by
  have htuple :
      tupleGetValue? (.tuple [burnPositionKeyValue I, .int 0, .int 0]) 0 =
        .ok (burnPositionKeyValue I) := rfl
  have hkey := burnPositionKeyValue_valueToKey I
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, positionsRef, tuple0,
    evalExpr?, burnPublicAfterModifiedFrame, burnPositionUpdateEvaledBaseRef,
    burnPositionKeyKey, htuple, hkey, EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem burnPublicAfterModified_resolvePositionRef {v : PoolImmutables}
    {evm I} :
    resolveStorageRef? (config v) (burnPublicAfterModifiedFrame v I) evm
      (positionsRef (tuple0 (.var "modified"))) =
        .ok (burnPositionUpdateEvaledBaseRef I, positionInfoStructTy) := by
  apply resolveStorageRef?_ok
  · exact burnPublicAfterModified_positions (v := v) I
  · exact burnPublicAfterModified_evalStorageRef_positions (v := v) evm I
  · simp [burnPositionUpdateEvaledBaseRef, burnPositionKeyKey, contract, storageDecls,
      storageTypeAt?, storageTypeStep?, positionInfoStructTy]

theorem burnPublicAfterPosition_modified {v : PoolImmutables} (I : ExecutionEnv) :
    (burnPublicAfterPositionFrame v I).locals.get? "modified" =
      some (.tuple [burnPositionKeyValue I, .int 0, .int 0]) := by
  rw [burnPublicAfterPositionFrame]
  rw [store_get_ne (burnPublicAfterModifiedFrame v I).locals
    (k := "position") (a := "modified")
    (.storageRef (burnPositionUpdateEvaledBaseRef I) positionInfoStructTy) (by native_decide)]
  rw [burnPublicAfterModifiedFrame]
  exact store_get_self (burnLiquidityDeltaFrame v I).locals "modified"
    (.tuple [burnPositionKeyValue I, .int 0, .int 0])

theorem burnPublicAfterAmount0_modified {v : PoolImmutables} (I : ExecutionEnv) :
    (burnPublicAfterAmount0Frame v I).locals.get? "modified" =
      some (.tuple [burnPositionKeyValue I, .int 0, .int 0]) := by
  rw [burnPublicAfterAmount0Frame]
  rw [store_get_ne (burnPublicAfterPositionFrame v I).locals
    (k := "amount0") (a := "modified") (.int 0) (by native_decide)]
  exact burnPublicAfterPosition_modified (v := v) I

theorem burnPublicAfterPosition_evalModifiedTuple1 {v : PoolImmutables} {evm I} :
    evalExpr? (config v) (burnPublicAfterPositionFrame v I) evm (tuple1 (.var "modified")) =
      .ok (.int 0) := by
  simp only [tuple1, evalExpr?, EvalResult.bind, bind]
  rw [burnPublicAfterPosition_modified (v := v) I]
  rfl

theorem burnPublicAfterAmount0_evalModifiedTuple2 {v : PoolImmutables} {evm I} :
    evalExpr? (config v) (burnPublicAfterAmount0Frame v I) evm (tuple2 (.var "modified")) =
      .ok (.int 0) := by
  simp only [tuple2, evalExpr?, EvalResult.bind, bind]
  rw [burnPublicAfterAmount0_modified (v := v) I]
  rfl

theorem burnPublicAfterPosition_evalAmount0 {v : PoolImmutables} {evm I} :
    evalExpr? (config v) (burnPublicAfterPositionFrame v I) evm
      (uint256Wrap (subE (.intLit 0) (tuple1 (.var "modified")))) = .ok (.int 0) := by
  simp only [uint256Wrap, modE, subE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPublicAfterPosition_evalModifiedTuple1 (v := v) (evm := evm) (I := I)]
  simp [uint256Modulus, evalExpr?, evalBinaryOp?, pure]

theorem burnPublicAfterAmount0_evalAmount1 {v : PoolImmutables} {evm I} :
    evalExpr? (config v) (burnPublicAfterAmount0Frame v I) evm
      (uint256Wrap (subE (.intLit 0) (tuple2 (.var "modified")))) = .ok (.int 0) := by
  simp only [uint256Wrap, modE, subE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPublicAfterAmount0_evalModifiedTuple2 (v := v) (evm := evm) (I := I)]
  simp [uint256Modulus, evalExpr?, evalBinaryOp?, pure]

theorem burnPublicAfterAmount1_amount0 {v : PoolImmutables} (I : ExecutionEnv) :
    (burnPublicAfterAmount1Frame v I).locals.get? "amount0" = some (.int 0) := by
  rw [burnPublicAfterAmount1Frame]
  rw [store_get_ne (burnPublicAfterAmount0Frame v I).locals
    (k := "amount1") (a := "amount0") (.int 0) (by native_decide)]
  rw [burnPublicAfterAmount0Frame]
  exact store_get_self (burnPublicAfterPositionFrame v I).locals "amount0" (.int 0)

theorem burnPublicAfterAmount1_amount1 {v : PoolImmutables} (I : ExecutionEnv) :
    (burnPublicAfterAmount1Frame v I).locals.get? "amount1" = some (.int 0) := by
  rw [burnPublicAfterAmount1Frame]
  exact store_get_self (burnPublicAfterAmount0Frame v I).locals "amount1" (.int 0)

theorem burnPublicAfterAmount1_evalAmountsPositiveFalse {v : PoolImmutables} {evm I} :
    evalExpr? (config v) (burnPublicAfterAmount1Frame v I) evm
      (orE (gtE (.var "amount0") (.intLit 0)) (gtE (.var "amount1") (.intLit 0))) =
        .ok (.bool false) := by
  simp only [orE, gtE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPublicAfterAmount1_amount0 (v := v) I]
  rw [burnPublicAfterAmount1_amount1 (v := v) I]
  simp [EvalResult.ofOption, evalBinaryOp?]

theorem burnPublicAfterAmount1_evalReturnValues {v : PoolImmutables} {evm I} :
    evalExprs? (config v) (burnPublicAfterAmount1Frame v I) evm
      [.var "amount0", .var "amount1"] = .ok [.int 0, .int 0] := by
  simp only [evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnPublicAfterAmount1_amount0 (v := v) I]
  rw [burnPublicAfterAmount1_amount1 (v := v) I]
  rfl

theorem burnPublicAfterAmount1_noSlot0 {v : PoolImmutables} (I : ExecutionEnv) :
    "slot0" ∉ (burnPublicAfterAmount1Frame v I).locals := by
  rw [burnPublicAfterAmount1Frame, burnPublicAfterAmount0Frame,
    burnPublicAfterPositionFrame, burnPublicAfterModifiedFrame, burnLiquidityDeltaFrame, burnStore]
  simp

theorem uniswapV3PoolBurnSourceAfterModifyPositionZeroTail
    {v : PoolImmutables} {evm I} :
    ExecBlock (config v) (burnPublicAfterModifiedFrame v I) evm
      [ .letStorage "position" (positionsRef (tuple0 (.var "modified"))),
        .letDecl "amount0" (some uint256)
          (uint256Wrap (subE (.intLit 0) (tuple1 (.var "modified")))),
        .letDecl "amount1" (some uint256)
          (uint256Wrap (subE (.intLit 0) (tuple2 (.var "modified")))),
        Stmt.ite (orE (gtE (.var "amount0") (.intLit 0))
            (gtE (.var "amount1") (.intLit 0)))
          [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
              (addE (.field (.var "position") "tokensOwed0") (uint128Wrap (.var "amount0"))),
            .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
              (addE (.field (.var "position") "tokensOwed1") (uint128Wrap (.var "amount1"))) ]
          [],
        .assign .storage (slot0F "unlocked") (.boolLit true),
        .return [.var "amount0", .var "amount1"] ]
      (.returned (burnPublicAfterAmount1Frame v I) (slot0AfterUnlockState evm)
        (some [.int 0, .int 0])) := by
  refine ExecBlock.consNormal
    (ExecStmt.letStorage (burnPublicAfterModified_resolvePositionRef (v := v))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnPublicAfterPosition_evalAmount0 (v := v) (evm := evm) (I := I))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnPublicAfterAmount0_evalAmount1 (v := v) (evm := evm) (I := I))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.iteFalse
      (burnPublicAfterAmount1_evalAmountsPositiveFalse (v := v) (evm := evm) (I := I))
      ExecBlock.nil) ?_
  refine ExecBlock.consNormal
    (ExecStmt.assign (by simp [evalExpr?, pure])
      (assignStorageRef_burn_unlocked_true (v := v) evm
        (burnPublicAfterAmount1Frame v I).locals
        (burnPublicAfterAmount1_noSlot0 (v := v) I))) ?_
  exact ExecBlock.consReturn
    (ExecStmt.return (burnPublicAfterAmount1_evalReturnValues (v := v)
      (evm := slot0AfterUnlockState evm) (I := I)))

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnSourceZeroDeltaReturnsZeroTokens
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hinside0 :
      burnTickGetInside0Value
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I =
        .int (Int.ofNat feeGrowthInside0X128.toNat))
    (hinside1 :
      burnTickGetInside1Value
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I =
        .int (Int.ofNat feeGrowthInside1X128.toNat))
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
            I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (htokens0 :
      burnPositionUpdateSourceTokensOwed0Int
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I
          (Int.ofNat feeGrowthInside0X128.toNat) = 0)
    (htokens1 :
      burnPositionUpdateSourceTokensOwed1Int
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I
          (Int.ofNat feeGrowthInside1X128.toNat) = 0) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I) burnTransition.body
      (.returned (burnPublicAfterAmount1Frame v I)
        (slot0AfterUnlockState
          (Solm.EVM.storageStore
            (Solm.EVM.storageStore
              (initState cA gh bl
                (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) σ₀ g A I)
              I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
              feeGrowthInside0X128)
            I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
            feeGrowthInside1X128))
        (some [.int 0, .int 0])) := by
  refine ExecFuncBody.execBlockRet ?_
  let lockedσ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)
  let evmFees :=
    Solm.EVM.storageStore
      (Solm.EVM.storageStore (initState cA gh bl lockedσ σ₀ g A I)
        I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
      I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1X128
  have hprefix := uniswapV3PoolBurnSourceThroughLiquidityDelta (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked hcanon
  have hlockState :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I) =
        initState cA gh bl lockedσ σ₀ g A I := by
    unfold lockedσ
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
        (.ok (burnPublicAfterModifiedFrame v I) evmFees) := by
    rw [hlockState]
    have hbody := uniswapV3PoolModifyPositionSourceZeroDeltaReturnsZeroTokens
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := lockedσ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
      (by simpa [lockedσ] using hinside0) (by simpa [lockedσ] using hinside1)
      hguard htickLt hge hle hzero (by simpa [lockedσ] using hliq)
      (by simpa [lockedσ] using htokens0) (by simpa [lockedσ] using htokens1)
    refine internalCallFunctionReturn (callee := modifyPositionFunction v)
      (retVar := "modified")
      (argVals := burnModifyPositionArgValues I) (locals := burnModifyPositionStore I)
      (calleeSolm := burnModifyPositionAfterAmount1Frame v lockedσ I)
      (value := some [burnPositionKeyValue I, .int 0, .int 0]) ?_ ?_ ?_ ?_
    · have hLower := burnLiquidityDeltaFrame_tickLower (v := v) I
      have hUpper := burnLiquidityDeltaFrame_tickUpper (v := v) I
      have hDelta := burnLiquidityDeltaFrame_liquidityDelta (v := v) I
      simp only [burnModifyPositionArgValues, evalExprs?, evalExpr?, envValue, initState,
        EvalResult.bind, bind, pure]
      rw [hLower, hUpper, hDelta]
      rfl
    · simpa [burnLiquidityDeltaFrame] using uniswapV3PoolLookupModifyPosition v
    · rfl
    · simpa [evmFees] using hbody
  have htail :
      ExecBlock (config v) (burnLiquidityDeltaFrame v I)
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))
        ([ .internalCall "modifyPosition"
            [.env .caller, .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
            "modified" ] ++
          [ .letStorage "position" (positionsRef (tuple0 (.var "modified"))),
            .letDecl "amount0" (some uint256)
              (uint256Wrap (subE (.intLit 0) (tuple1 (.var "modified")))),
            .letDecl "amount1" (some uint256)
              (uint256Wrap (subE (.intLit 0) (tuple2 (.var "modified")))),
            Stmt.ite (orE (gtE (.var "amount0") (.intLit 0))
                (gtE (.var "amount1") (.intLit 0)))
              [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
                  (addE (.field (.var "position") "tokensOwed0")
                    (uint128Wrap (.var "amount0"))),
                .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
                  (addE (.field (.var "position") "tokensOwed1")
                    (uint128Wrap (.var "amount1"))) ]
              [],
            .assign .storage (slot0F "unlocked") (.boolLit true),
            .return [.var "amount0", .var "amount1"] ])
        (.returned (burnPublicAfterAmount1Frame v I) (slot0AfterUnlockState evmFees)
          (some [.int 0, .int 0])) := by
    refine ExecBlock.consNormal hstmt ?_
    exact uniswapV3PoolBurnSourceAfterModifyPositionZeroTail
      (v := v) (evm := evmFees) (I := I)
  simpa [burnTransition, nonpayable, lockPrefix, lockSuffix, evmFees, lockedσ]
    using execBlock_append hprefix htail

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnSourceZeroDeltaReturnsTokensOwed
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (feeGrowthInside0X128 feeGrowthInside1X128 : UInt256)
    (hwv : I.weiValue = ⟨0⟩)
    (hunlocked : burnUnlockedByte σ I ≠ ⟨0⟩)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hinside0 :
      burnTickGetInside0Value
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I =
        .int (Int.ofNat feeGrowthInside0X128.toNat))
    (hinside1 :
      burnTickGetInside1Value
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I =
        .int (Int.ofNat feeGrowthInside1X128.toNat))
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
          (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
            I (positionsBase (burnPositionKeyKey I))) ≠ ⟨0⟩)
    (hcond :
      evalExpr? (config v)
        (burnPositionUpdateValueAfterTokensOwed1Frame v
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I
          (Int.ofNat feeGrowthInside0X128.toNat) (Int.ofNat feeGrowthInside1X128.toNat))
        (Solm.EVM.storageStore
          (Solm.EVM.storageStore
            (initState cA gh bl
              (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) σ₀ g A I)
            I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
            feeGrowthInside0X128)
          I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
          feeGrowthInside1X128)
        (orE (gtE (.var "tokensOwed0") (.intLit 0))
          (gtE (.var "tokensOwed1") (.intLit 0))) = .ok (.bool true)) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I) burnTransition.body
      (.returned (burnPublicAfterAmount1Frame v I)
        (slot0AfterUnlockState
          (burnPositionUpdateSourceAfterTokensOwedState
            (Solm.EVM.storageStore
              (Solm.EVM.storageStore
                (initState cA gh bl
                  (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) σ₀ g A I)
                I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨1⟩)
                feeGrowthInside0X128)
              I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩)
              feeGrowthInside1X128)
            (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I
            feeGrowthInside0X128 feeGrowthInside1X128))
        (some [.int 0, .int 0])) := by
  refine ExecFuncBody.execBlockRet ?_
  let lockedσ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)
  let evmFees :=
    Solm.EVM.storageStore
      (Solm.EVM.storageStore (initState cA gh bl lockedσ σ₀ g A I)
        I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨1⟩) feeGrowthInside0X128)
      I.codeOwner (positionsBase (burnPositionKeyKey I) + ⟨2⟩) feeGrowthInside1X128
  let evmTokens := burnPositionUpdateSourceAfterTokensOwedState evmFees lockedσ I
    feeGrowthInside0X128 feeGrowthInside1X128
  have hprefix := uniswapV3PoolBurnSourceThroughLiquidityDelta (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hwv hunlocked hcanon
  have hlockState :
      Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I) =
        initState cA gh bl lockedσ σ₀ g A I := by
    unfold lockedσ
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
        (.ok (burnPublicAfterModifiedFrame v I) evmTokens) := by
    rw [hlockState]
    have hbody := uniswapV3PoolModifyPositionSourceZeroDeltaReturnsTokensOwed
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := lockedσ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) feeGrowthInside0X128 feeGrowthInside1X128
      (by simpa [lockedσ] using hinside0) (by simpa [lockedσ] using hinside1)
      hguard htickLt hge hle hzero (by simpa [lockedσ] using hliq)
      (by simpa [lockedσ, evmFees] using hcond)
    refine internalCallFunctionReturn (callee := modifyPositionFunction v)
      (retVar := "modified")
      (argVals := burnModifyPositionArgValues I) (locals := burnModifyPositionStore I)
      (calleeSolm := burnModifyPositionAfterAmount1Frame v lockedσ I)
      (value := some [burnPositionKeyValue I, .int 0, .int 0]) ?_ ?_ ?_ ?_
    · have hLower := burnLiquidityDeltaFrame_tickLower (v := v) I
      have hUpper := burnLiquidityDeltaFrame_tickUpper (v := v) I
      have hDelta := burnLiquidityDeltaFrame_liquidityDelta (v := v) I
      simp only [burnModifyPositionArgValues, evalExprs?, evalExpr?, envValue, initState,
        EvalResult.bind, bind, pure]
      rw [hLower, hUpper, hDelta]
      rfl
    · simpa [burnLiquidityDeltaFrame] using uniswapV3PoolLookupModifyPosition v
    · rfl
    · simpa [evmTokens] using hbody
  have htail :
      ExecBlock (config v) (burnLiquidityDeltaFrame v I)
        (Solm.EVM.storageStore (initState cA gh bl σ σ₀ g A I) I.codeOwner ⟨0⟩
          (burnLockedSlotWord σ I))
        ([ .internalCall "modifyPosition"
            [.env .caller, .var "tickLower", .var "tickUpper", .var "liquidityDelta"]
            "modified" ] ++
          [ .letStorage "position" (positionsRef (tuple0 (.var "modified"))),
            .letDecl "amount0" (some uint256)
              (uint256Wrap (subE (.intLit 0) (tuple1 (.var "modified")))),
            .letDecl "amount1" (some uint256)
              (uint256Wrap (subE (.intLit 0) (tuple2 (.var "modified")))),
            Stmt.ite (orE (gtE (.var "amount0") (.intLit 0))
                (gtE (.var "amount1") (.intLit 0)))
              [ .assign .storage { base := "position", steps := [.field "tokensOwed0"] }
                  (addE (.field (.var "position") "tokensOwed0")
                    (uint128Wrap (.var "amount0"))),
                .assign .storage { base := "position", steps := [.field "tokensOwed1"] }
                  (addE (.field (.var "position") "tokensOwed1")
                    (uint128Wrap (.var "amount1"))) ]
              [],
            .assign .storage (slot0F "unlocked") (.boolLit true),
            .return [.var "amount0", .var "amount1"] ])
        (.returned (burnPublicAfterAmount1Frame v I) (slot0AfterUnlockState evmTokens)
          (some [.int 0, .int 0])) := by
    refine ExecBlock.consNormal hstmt ?_
    exact uniswapV3PoolBurnSourceAfterModifyPositionZeroTail
      (v := v) (evm := evmTokens) (I := I)
  simpa [burnTransition, nonpayable, lockPrefix, lockSuffix, evmFees, evmTokens, lockedσ]
    using execBlock_append hprefix htail

end Benchmarks.UniswapV3Pool
