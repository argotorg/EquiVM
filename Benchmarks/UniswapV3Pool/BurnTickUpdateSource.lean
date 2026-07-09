import Benchmarks.UniswapV3Pool.BurnTickUpdateStart
import Benchmarks.UniswapV3Pool.BurnLiquidityAddDelta

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev burnTickUpdateLowerInfoFrame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickUpdateLowerStore v σ I).insert "info"
      (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy) }

abbrev burnTickUpdateLowerLiquidityGrossBeforeWord (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.land (solcSlotWord σ I (burnTickGetLowerBaseSlot I)) uint128Mask

abbrev burnTickUpdateLowerLiquidityGrossBeforeValue (σ : AccountMap)
    (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (burnTickUpdateLowerLiquidityGrossBeforeWord σ I).toNat)

abbrev burnTickUpdateLowerLiquidityGrossBeforeInt (σ : AccountMap)
    (I : ExecutionEnv) : Int :=
  Int.ofNat (burnTickUpdateLowerLiquidityGrossBeforeWord σ I).toNat

abbrev burnTickUpdateLowerLiquidityDeltaInt (I : ExecutionEnv) : Int :=
  0 - Int.ofNat (burnAmountCleanWord I).toNat

abbrev burnTickUpdateLowerLiquidityAddDeltaArgValues (σ : AccountMap)
    (I : ExecutionEnv) : List Value :=
  liquidityAddDeltaArgValues
    (burnTickUpdateLowerLiquidityGrossBeforeInt σ I)
    (burnTickUpdateLowerLiquidityDeltaInt I)

abbrev burnTickUpdateLowerAfterLiquidityGrossBeforeFrame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickUpdateLowerInfoFrame v σ I).locals.insert
      "liquidityGrossBefore" (burnTickUpdateLowerLiquidityGrossBeforeValue σ I) }

abbrev burnTickUpdateLowerLiquidityGrossAfterSubInt (σ : AccountMap)
    (I : ExecutionEnv) : Int :=
  liquidityAddDeltaWrappedSub
    (burnTickUpdateLowerLiquidityGrossBeforeInt σ I)
    (burnTickUpdateLowerLiquidityDeltaInt I)

abbrev burnTickUpdateLowerAfterLiquidityGrossAfterFrame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I).locals.insert
      "liquidityGrossAfter" (.int (burnTickUpdateLowerLiquidityGrossAfterSubInt σ I)) }

abbrev burnTickUpdateLowerFlippedBool (σ : AccountMap) (I : ExecutionEnv) : Bool :=
  decide ((burnTickUpdateLowerLiquidityGrossAfterSubInt σ I = 0) ≠
    (burnTickUpdateLowerLiquidityGrossBeforeInt σ I = 0))

abbrev burnTickUpdateLowerAfterFlippedFrame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I).locals.insert
      "flipped" (.bool (burnTickUpdateLowerFlippedBool σ I)) }

theorem burnTickUpdateLowerStore_tick {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickUpdateLowerStore v σ I).get? "tick" = some (burnTickLowerValue I) := by
  simp [burnTickUpdateLowerStore]

theorem burnTickUpdateLowerStore_ticks {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickUpdateLowerStore v σ I).get? "ticks" = none := by
  simp [burnTickUpdateLowerStore]

theorem burnTickUpdateLowerStore_maxLiquidity {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerStore v σ I).get? "maxLiquidity" =
      some (.int v.maxLiquidityPerTick) := by
  rw [burnTickUpdateLowerStore]
  let L0 : Store := (∅ : Store).insert "maxLiquidity" (.int v.maxLiquidityPerTick)
  let L1 : Store := (((((L0
    |>.insert "upper" (.bool false))
    |>.insert "time" (burnBlockTimestamp32Value I))
    |>.insert "tickCumulative" (wordToElem (.int int56Int)
      (burnObserveSingleTickStorageWord σ I)))
    |>.insert "secondsPerLiquidityCumulativeX128"
      (.int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat)))
    |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
  change ((((L1.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
      |>.insert "liquidityDelta" (burnLiquidityDeltaValue I))
      |>.insert "tickCurrent" (burnSlot0TickValue σ I))
      |>.insert "tick" (burnTickLowerValue I)).get? "maxLiquidity" =
    some (.int v.maxLiquidityPerTick)
  rw [store_get_ne4 L1 (k1 := "feeGrowthGlobal0X128") (k2 := "liquidityDelta")
    (k3 := "tickCurrent") (k4 := "tick") (a := "maxLiquidity")
    (burnFeeGrowthGlobal0Value σ I) (burnLiquidityDeltaValue I)
    (burnSlot0TickValue σ I) (burnTickLowerValue I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  rw [store_get_ne5 L0 (k1 := "upper") (k2 := "time") (k3 := "tickCumulative")
    (k4 := "secondsPerLiquidityCumulativeX128") (k5 := "feeGrowthGlobal1X128")
    (a := "maxLiquidity") (.bool false) (burnBlockTimestamp32Value I)
    (wordToElem (.int int56Int) (burnObserveSingleTickStorageWord σ I))
    (.int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat))
    (burnFeeGrowthGlobal1Value σ I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)]
  rw [store_get_self (∅ : Store) "maxLiquidity" (.int v.maxLiquidityPerTick)]

theorem burnTickUpdateLowerStore_liquidityDelta {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerStore v σ I).get? "liquidityDelta" =
      some (.int (burnTickUpdateLowerLiquidityDeltaInt I)) := by
  rw [burnTickUpdateLowerStore]
  let L0 : Store :=
    (((((((∅ : Store)
      |>.insert "maxLiquidity" (.int v.maxLiquidityPerTick))
      |>.insert "upper" (.bool false))
      |>.insert "time" (burnBlockTimestamp32Value I))
      |>.insert "tickCumulative" (wordToElem (.int int56Int)
        (burnObserveSingleTickStorageWord σ I)))
      |>.insert "secondsPerLiquidityCumulativeX128"
        (.int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat)))
      |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
      |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I)
  change (((L0.insert "liquidityDelta" (burnLiquidityDeltaValue I))
      |>.insert "tickCurrent" (burnSlot0TickValue σ I))
      |>.insert "tick" (burnTickLowerValue I)).get? "liquidityDelta" =
    some (.int (burnTickUpdateLowerLiquidityDeltaInt I))
  rw [store_get_ne2 (L0.insert "liquidityDelta" (burnLiquidityDeltaValue I))
    (k1 := "tickCurrent") (k2 := "tick") (a := "liquidityDelta")
    (burnSlot0TickValue σ I) (burnTickLowerValue I)
    (by native_decide) (by native_decide)]
  rw [store_get_self L0 "liquidityDelta" (burnLiquidityDeltaValue I)]

theorem burnTickUpdateLower_evalStorageRef_info {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) :
    evalStorageRef (config v) (burnTickUpdateLowerFrame v σ I) evm
      (ticksRef (.var "tick")) =
        .ok (burnTickGetLowerEvaledBaseRef I) := by
  simp only [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, ticksRef,
    burnTickUpdateLowerFrame, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnTickUpdateLowerStore_tick]
  simp [burnTickGetLowerEvaledBaseRef, burnTickGetLowerKey, burnTickLowerValue,
    valueToKey?, EvalResult.ofOption]

theorem burnTickUpdateLower_resolveInfoRef {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    resolveStorageRef? (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I) (ticksRef (.var "tick")) =
        .ok (burnTickGetLowerEvaledBaseRef I, tickInfoStructTy) := by
  apply resolveStorageRef?_ok
  · exact burnTickUpdateLowerStore_ticks σ I
  · exact burnTickUpdateLower_evalStorageRef_info (v := v)
      (initState cA gh bl σ σ₀ g A I) σ I
  · simp [burnTickGetLowerEvaledBaseRef, contract, storageDecls, storageTypeAt?,
      storageTypeStep?, tickInfoStructTy]

theorem burnTickUpdateLowerInfoFrame_info {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickUpdateLowerInfoFrame v σ I).locals.get? "info" =
      some (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy) := by
  rw [burnTickUpdateLowerInfoFrame]
  exact store_get_self (burnTickUpdateLowerStore v σ I) "info"
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)

theorem burnTickUpdateLowerInfoFrame_liquidityDelta {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerInfoFrame v σ I).locals.get? "liquidityDelta" =
      some (.int (burnTickUpdateLowerLiquidityDeltaInt I)) := by
  rw [burnTickUpdateLowerInfoFrame]
  rw [store_get_ne (burnTickUpdateLowerStore v σ I)
    (k := "info") (a := "liquidityDelta")
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  exact burnTickUpdateLowerStore_liquidityDelta σ I

theorem burnTickUpdateLower_evalLiquidityGrossBefore {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnTickUpdateLowerInfoFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "info") "liquidityGross") =
        .ok (burnTickUpdateLowerLiquidityGrossBeforeValue σ I) := by
  simp only [evalExpr?, EvalResult.bind, bind]
  rw [burnTickUpdateLowerInfoFrame_info]
  change readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
    (burnTickGetLowerEvaledRef I "liquidityGross") uint128St =
      .ok (burnTickUpdateLowerLiquidityGrossBeforeValue σ I)
  rw [show uint128St = .elem (.int uint128Int) by rfl]
  rw [readStorage?_elem
    (er := burnTickGetLowerEvaledRef I "liquidityGross")
    (t := .int uint128Int)
    (loc := loc (burnTickGetLowerBaseSlot I) ⟨0, by decide⟩
      ⟨16, by decide⟩ (by decide) (.int uint128Int))]
  · simpa [initState, burnTickUpdateLowerLiquidityGrossBeforeValue,
      burnTickUpdateLowerLiquidityGrossBeforeWord, solcSlotWord, loc] using
      storageLocLoad_uint_offset0 (initState cA gh bl σ σ₀ g A I)
        (burnTickGetLowerBaseSlot I) ⟨16, by decide⟩ ⟨128, by decide⟩
        (hbound := by decide) (by decide)
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnTickGetLowerEvaledRef, burnTickGetLowerBaseSlot, loc]

theorem burnTickUpdateLowerAfterLiquidityGrossBeforeFrame_liquidityGrossBefore
    {v : PoolImmutables} (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I).locals.get?
      "liquidityGrossBefore" =
        some (.int (burnTickUpdateLowerLiquidityGrossBeforeInt σ I)) := by
  rw [burnTickUpdateLowerAfterLiquidityGrossBeforeFrame,
    burnTickUpdateLowerLiquidityGrossBeforeValue,
    burnTickUpdateLowerLiquidityGrossBeforeInt]
  exact store_get_self (burnTickUpdateLowerInfoFrame v σ I).locals
    "liquidityGrossBefore"
    (.int (Int.ofNat (burnTickUpdateLowerLiquidityGrossBeforeWord σ I).toNat))

theorem burnTickUpdateLowerAfterLiquidityGrossBeforeFrame_liquidityDelta
    {v : PoolImmutables} (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I).locals.get?
      "liquidityDelta" = some (.int (burnTickUpdateLowerLiquidityDeltaInt I)) := by
  rw [burnTickUpdateLowerAfterLiquidityGrossBeforeFrame]
  rw [store_get_ne (burnTickUpdateLowerInfoFrame v σ I).locals
    (k := "liquidityGrossBefore") (a := "liquidityDelta")
    (burnTickUpdateLowerLiquidityGrossBeforeValue σ I) (by native_decide)]
  exact burnTickUpdateLowerInfoFrame_liquidityDelta σ I

theorem burnTickUpdateLowerAfterLiquidityGrossAfterFrame_liquidityGrossAfter
    {v : PoolImmutables} (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I).locals.get?
      "liquidityGrossAfter" =
        some (.int (burnTickUpdateLowerLiquidityGrossAfterSubInt σ I)) := by
  rw [burnTickUpdateLowerAfterLiquidityGrossAfterFrame]
  exact store_get_self (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I).locals
    "liquidityGrossAfter" (.int (burnTickUpdateLowerLiquidityGrossAfterSubInt σ I))

theorem burnTickUpdateLowerAfterLiquidityGrossAfterFrame_liquidityGrossBefore
    {v : PoolImmutables} (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I).locals.get?
      "liquidityGrossBefore" =
        some (.int (burnTickUpdateLowerLiquidityGrossBeforeInt σ I)) := by
  rw [burnTickUpdateLowerAfterLiquidityGrossAfterFrame]
  rw [store_get_ne (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I).locals
    (k := "liquidityGrossAfter") (a := "liquidityGrossBefore")
    (.int (burnTickUpdateLowerLiquidityGrossAfterSubInt σ I)) (by native_decide)]
  exact burnTickUpdateLowerAfterLiquidityGrossBeforeFrame_liquidityGrossBefore σ I

theorem burnTickUpdateLowerAfterLiquidityGrossAfterFrame_maxLiquidity
    {v : PoolImmutables} (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I).locals.get?
      "maxLiquidity" = some (.int v.maxLiquidityPerTick) := by
  rw [burnTickUpdateLowerAfterLiquidityGrossAfterFrame,
    burnTickUpdateLowerAfterLiquidityGrossBeforeFrame, burnTickUpdateLowerInfoFrame]
  rw [store_get_ne3 (burnTickUpdateLowerStore v σ I)
    (k1 := "info") (k2 := "liquidityGrossBefore") (k3 := "liquidityGrossAfter")
    (a := "maxLiquidity")
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)
    (burnTickUpdateLowerLiquidityGrossBeforeValue σ I)
    (.int (burnTickUpdateLowerLiquidityGrossAfterSubInt σ I))
    (by native_decide) (by native_decide) (by native_decide)]
  exact burnTickUpdateLowerStore_maxLiquidity σ I

theorem burnTickUpdateLowerAfterFlippedFrame_flipped
    {v : PoolImmutables} (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerAfterFlippedFrame v σ I).locals.get? "flipped" =
      some (.bool (burnTickUpdateLowerFlippedBool σ I)) := by
  rw [burnTickUpdateLowerAfterFlippedFrame]
  exact store_get_self (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I).locals
    "flipped" (.bool (burnTickUpdateLowerFlippedBool σ I))

theorem burnTickUpdateLowerAfterFlippedFrame_liquidityGrossBefore
    {v : PoolImmutables} (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpdateLowerAfterFlippedFrame v σ I).locals.get? "liquidityGrossBefore" =
      some (.int (burnTickUpdateLowerLiquidityGrossBeforeInt σ I)) := by
  rw [burnTickUpdateLowerAfterFlippedFrame]
  rw [store_get_ne (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I).locals
    (k := "flipped") (a := "liquidityGrossBefore")
    (.bool (burnTickUpdateLowerFlippedBool σ I)) (by native_decide)]
  exact burnTickUpdateLowerAfterLiquidityGrossAfterFrame_liquidityGrossBefore σ I

theorem burnTickUpdateLower_evalLiquidityAddDeltaArgs
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExprs? (config v) (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [.var "liquidityGrossBefore", .var "liquidityDelta"] =
        .ok (burnTickUpdateLowerLiquidityAddDeltaArgValues σ I) := by
  simp only [burnTickUpdateLowerLiquidityAddDeltaArgValues, liquidityAddDeltaArgValues,
    evalExprs?, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnTickUpdateLowerAfterLiquidityGrossBeforeFrame_liquidityGrossBefore,
    burnTickUpdateLowerAfterLiquidityGrossBeforeFrame_liquidityDelta]
  rfl

theorem burnTickUpdateLowerLiquidityDeltaNegative (I : ExecutionEnv)
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩) :
    burnTickUpdateLowerLiquidityDeltaInt I < 0 := by
  have hnat : (burnAmountCleanWord I).toNat ≠ 0 := by
    intro hzero
    exact hnonzero (uint256_toNat_eq_zero hzero)
  have hpos : 0 < (burnAmountCleanWord I).toNat := Nat.pos_of_ne_zero hnat
  unfold burnTickUpdateLowerLiquidityDeltaInt
  change 0 - ((burnAmountCleanWord I).toNat : Int) < 0
  have hposInt : (0 : Int) < ((burnAmountCleanWord I).toNat : Int) := by
    omega
  omega

theorem burnTickUpdateLower_evalLiquidityGrossAfterLeMaxTrue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick) :
    evalExpr? (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")) = .ok (.bool true) := by
  simp only [leE, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind]
  rw [burnTickUpdateLowerAfterLiquidityGrossAfterFrame_liquidityGrossAfter,
    burnTickUpdateLowerAfterLiquidityGrossAfterFrame_maxLiquidity]
  simp [evalBinaryOp?, hle]

theorem burnTickUpdateLower_evalLiquidityGrossAfterLeMaxFalse
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick) :
    evalExpr? (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")) = .ok (.bool false) := by
  simp only [leE, evalExpr?, EvalResult.bind, EvalResult.ofOption, bind]
  rw [burnTickUpdateLowerAfterLiquidityGrossAfterFrame_liquidityGrossAfter,
    burnTickUpdateLowerAfterLiquidityGrossAfterFrame_maxLiquidity]
  simp [evalBinaryOp?, hle]

theorem burnTickUpdateLower_evalFlipped
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (neE (eqE (.var "liquidityGrossAfter") (.intLit 0))
        (eqE (.var "liquidityGrossBefore") (.intLit 0))) =
        .ok (.bool (burnTickUpdateLowerFlippedBool σ I)) := by
  simp only [neE, eqE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnTickUpdateLowerAfterLiquidityGrossAfterFrame_liquidityGrossAfter,
    burnTickUpdateLowerAfterLiquidityGrossAfterFrame_liquidityGrossBefore]
  simp [EvalResult.ofOption, evalBinaryOp?, burnTickUpdateLowerFlippedBool]

theorem burnTickUpdateLower_evalLiquidityGrossBeforeEqZeroTrue
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : burnTickUpdateLowerLiquidityGrossBeforeInt σ I = 0) :
    evalExpr? (config v) (burnTickUpdateLowerAfterFlippedFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.var "liquidityGrossBefore") (.intLit 0)) = .ok (.bool true) := by
  simp only [eqE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnTickUpdateLowerAfterFlippedFrame_liquidityGrossBefore]
  have hnat : (burnTickUpdateLowerLiquidityGrossBeforeWord σ I).toNat = 0 := by
    unfold burnTickUpdateLowerLiquidityGrossBeforeInt at hzero
    exact Int.ofNat_eq_zero.mp hzero
  simp [EvalResult.ofOption, evalBinaryOp?, hnat]

theorem burnTickUpdateLower_evalLiquidityGrossBeforeEqZeroFalse
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnTickUpdateLowerLiquidityGrossBeforeInt σ I ≠ 0) :
    evalExpr? (config v) (burnTickUpdateLowerAfterFlippedFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (eqE (.var "liquidityGrossBefore") (.intLit 0)) = .ok (.bool false) := by
  simp only [eqE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnTickUpdateLowerAfterFlippedFrame_liquidityGrossBefore]
  have hnat : (burnTickUpdateLowerLiquidityGrossBeforeWord σ I).toNat ≠ 0 := by
    intro hz
    apply hnonzero
    unfold burnTickUpdateLowerLiquidityGrossBeforeInt
    simp [hz]
  simp [EvalResult.ofOption, evalBinaryOp?, hnat]

theorem uniswapV3PoolTickUpdateLowerSourceInfoStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecStmt (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.letStorage "info" (ticksRef (.var "tick")))
      (.ok (burnTickUpdateLowerInfoFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  exact ExecStmt.letStorage (burnTickUpdateLower_resolveInfoRef
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g))

theorem uniswapV3PoolTickUpdateLowerSourceLiquidityGrossBeforeStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecStmt (config v) (burnTickUpdateLowerInfoFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.letDecl "liquidityGrossBefore" (some uint128)
        (.field (.var "info") "liquidityGross"))
      (.ok (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  exact ExecStmt.letDecl (burnTickUpdateLower_evalLiquidityGrossBefore
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g))

theorem uniswapV3PoolTickUpdateLowerSourcePrefix
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecBlock (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "info" (ticksRef (.var "tick")),
        .letDecl "liquidityGrossBefore" (some uint128)
          (.field (.var "info") "liquidityGross") ]
      (.ok (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  exact ExecBlock.consNormal
    (uniswapV3PoolTickUpdateLowerSourceInfoStep
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g))
    (ExecBlock.consNormal
      (uniswapV3PoolTickUpdateLowerSourceLiquidityGrossBeforeStep
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g))
      ExecBlock.nil)

theorem uniswapV3PoolTickUpdateLowerSourceLiquidityAddDeltaReturnStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hreq :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I) :
    ExecStmt (config v) (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.internalCall "liquidityAddDelta"
        [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter")
      (.ok (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  let x := burnTickUpdateLowerLiquidityGrossBeforeInt σ I
  let y := burnTickUpdateLowerLiquidityDeltaInt I
  let z := burnTickUpdateLowerLiquidityGrossAfterSubInt σ I
  have hbody :
      ExecFuncBody (config v)
        { (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I) with
          locals := liquidityAddDeltaStore x y }
        (initState cA gh bl σ σ₀ g A I) liquidityAddDeltaFunction.body
        (.returned (liquidityAddDeltaAfterZFrame v x y z)
          (initState cA gh bl σ σ₀ g A I) (some [.int z])) := by
    have hy : y < 0 := by
      simpa [y] using burnTickUpdateLowerLiquidityDeltaNegative I hnonzero
    have hreq' : liquidityAddDeltaWrappedSub x y < x := by
      simpa [x, y, z, burnTickUpdateLowerLiquidityGrossAfterSubInt] using hreq
    simpa [liquidityAddDeltaFrame] using
      uniswapV3PoolLiquidityAddDeltaSourceNegativeReturns
        (v := v) (evm := initState cA gh bl σ σ₀ g A I)
        (x := x) (y := y) hy hreq'
  have hstmt := internalCallFunctionReturn (callee := liquidityAddDeltaFunction)
    (retVar := "liquidityGrossAfter")
    (argVals := burnTickUpdateLowerLiquidityAddDeltaArgValues σ I)
    (locals := liquidityAddDeltaStore x y)
    (calleeSolm := liquidityAddDeltaAfterZFrame v x y z)
    (value := some [.int z])
    (burnTickUpdateLower_evalLiquidityAddDeltaArgs (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g))
    (uniswapV3PoolLookupLiquidityAddDelta v)
    (by
      change bindParams? liquidityAddDeltaFunction.params
          (liquidityAddDeltaArgValues x y) = some (liquidityAddDeltaStore x y)
      exact liquidityAddDelta_bindParams x y)
    hbody
  simpa [burnTickUpdateLowerAfterLiquidityGrossAfterFrame, resumeAfterInternalCall,
    collapseReturns, x, y, z] using hstmt

theorem uniswapV3PoolTickUpdateLowerSourceLiquidityAddDeltaRevertStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hreq :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I) :
    ExecStmt (config v) (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.internalCall "liquidityAddDelta"
        [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter")
      .reverted := by
  let x := burnTickUpdateLowerLiquidityGrossBeforeInt σ I
  let y := burnTickUpdateLowerLiquidityDeltaInt I
  have hbody :
      ExecFuncBody (config v)
        { (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I) with
          locals := liquidityAddDeltaStore x y }
        (initState cA gh bl σ σ₀ g A I) liquidityAddDeltaFunction.body
        .reverted := by
    have hy : y < 0 := by
      simpa [y] using burnTickUpdateLowerLiquidityDeltaNegative I hnonzero
    have hreq' : ¬ liquidityAddDeltaWrappedSub x y < x := by
      simpa [x, y, burnTickUpdateLowerLiquidityGrossAfterSubInt] using hreq
    simpa [liquidityAddDeltaFrame] using
      uniswapV3PoolLiquidityAddDeltaSourceNegativeReverts
        (v := v) (evm := initState cA gh bl σ σ₀ g A I)
        (x := x) (y := y) hy hreq'
  exact internalCallFunctionRevert (callee := liquidityAddDeltaFunction)
    (argVals := burnTickUpdateLowerLiquidityAddDeltaArgValues σ I)
    (locals := liquidityAddDeltaStore x y)
    (burnTickUpdateLower_evalLiquidityAddDeltaArgs (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I)
      (g := g))
    (uniswapV3PoolLookupLiquidityAddDelta v)
    (by
      change bindParams? liquidityAddDeltaFunction.params
          (liquidityAddDeltaArgValues x y) = some (liquidityAddDeltaStore x y)
      exact liquidityAddDelta_bindParams x y)
    hbody

theorem uniswapV3PoolTickUpdateLowerSourceThroughLiquidityAddDeltaReturnPrefix
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hreq :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I) :
    ExecBlock (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "info" (ticksRef (.var "tick")),
        .letDecl "liquidityGrossBefore" (some uint128)
          (.field (.var "info") "liquidityGross"),
        .internalCall "liquidityAddDelta"
          [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter" ]
      (.ok (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolTickUpdateLowerSourcePrefix
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
  have htail :
      ExecBlock (config v) (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        [ .internalCall "liquidityAddDelta"
            [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter" ]
        (.ok (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (uniswapV3PoolTickUpdateLowerSourceLiquidityAddDeltaReturnStep
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hnonzero hreq)
      ExecBlock.nil
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolTickUpdateLowerSourceLiquidityAddDeltaRevertPrefix
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hreq :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I)
    (rest : List Stmt) :
    ExecBlock (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.letStorage "info" (ticksRef (.var "tick")) ::
        .letDecl "liquidityGrossBefore" (some uint128)
          (.field (.var "info") "liquidityGross") ::
        .internalCall "liquidityAddDelta"
          [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter" ::
        rest)
      .reverted := by
  have hprefix := uniswapV3PoolTickUpdateLowerSourcePrefix
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)
  have htail :
      ExecBlock (config v) (burnTickUpdateLowerAfterLiquidityGrossBeforeFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        (.internalCall "liquidityAddDelta"
            [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter" ::
          rest)
        .reverted := by
    exact ExecBlock.consRevert
      (uniswapV3PoolTickUpdateLowerSourceLiquidityAddDeltaRevertStep
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hnonzero hreq)
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolTickUpdateLowerSourceMaxLiquidityStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick) :
    ExecStmt (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")))
      (.ok (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  exact ExecStmt.requireTrue
    (burnTickUpdateLower_evalLiquidityGrossAfterLeMaxTrue
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hle)

theorem uniswapV3PoolTickUpdateLowerSourceMaxLiquidityRevertStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hle :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick) :
    ExecStmt (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")))
      .reverted := by
  exact ExecStmt.requireFalse
    (burnTickUpdateLower_evalLiquidityGrossAfterLeMaxFalse
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hle)

theorem uniswapV3PoolTickUpdateLowerSourceFlippedStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecStmt (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.letDecl "flipped" (some boolTy)
        (neE (eqE (.var "liquidityGrossAfter") (.intLit 0))
          (eqE (.var "liquidityGrossBefore") (.intLit 0))))
      (.ok (burnTickUpdateLowerAfterFlippedFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  exact ExecStmt.letDecl
    (burnTickUpdateLower_evalFlipped
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g))

theorem uniswapV3PoolTickUpdateLowerSourceLiquidityGrossBeforeNonzeroStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbefore : burnTickUpdateLowerLiquidityGrossBeforeInt σ I ≠ 0) :
    ExecStmt (config v) (burnTickUpdateLowerAfterFlippedFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (Stmt.ite (eqE (.var "liquidityGrossBefore") (.intLit 0))
        [ Stmt.ite (leE (.var "tick") (.var "tickCurrent"))
            [ .assign .storage { base := "info", steps := [.field "feeGrowthOutside0X128"] }
                (.var "feeGrowthGlobal0X128"),
              .assign .storage { base := "info", steps := [.field "feeGrowthOutside1X128"] }
                (.var "feeGrowthGlobal1X128"),
              .assign .storage
                { base := "info", steps := [.field "secondsPerLiquidityOutsideX128"] }
                (.var "secondsPerLiquidityCumulativeX128"),
              .assign .storage { base := "info", steps := [.field "tickCumulativeOutside"] }
                (.var "tickCumulative"),
              .assign .storage { base := "info", steps := [.field "secondsOutside"] }
                (.var "time") ]
            [],
          .assign .storage { base := "info", steps := [.field "initialized"] } (.boolLit true) ]
        [])
      (.ok (burnTickUpdateLowerAfterFlippedFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  exact ExecStmt.iteFalse
    (burnTickUpdateLower_evalLiquidityGrossBeforeEqZeroFalse
      (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hbefore)
    ExecBlock.nil

theorem uniswapV3PoolTickUpdateLowerSourceThroughMaxLiquidity
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hdelta :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I)
    (hle :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick) :
    ExecBlock (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "info" (ticksRef (.var "tick")),
        .letDecl "liquidityGrossBefore" (some uint128)
          (.field (.var "info") "liquidityGross"),
        .internalCall "liquidityAddDelta"
          [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter",
        .require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")) ]
      (.ok (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolTickUpdateLowerSourceThroughLiquidityAddDeltaReturnPrefix
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hnonzero hdelta
  have htail :
      ExecBlock (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        [ .require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")) ]
        (.ok (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (uniswapV3PoolTickUpdateLowerSourceMaxLiquidityStep
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
      (A := A) (I := I) (g := g) hle)
      ExecBlock.nil
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolTickUpdateLowerSourceThroughFlipped
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hdelta :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I)
    (hle :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick) :
    ExecBlock (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "info" (ticksRef (.var "tick")),
        .letDecl "liquidityGrossBefore" (some uint128)
          (.field (.var "info") "liquidityGross"),
        .internalCall "liquidityAddDelta"
          [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter",
        .require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")),
        .letDecl "flipped" (some boolTy)
          (neE (eqE (.var "liquidityGrossAfter") (.intLit 0))
            (eqE (.var "liquidityGrossBefore") (.intLit 0))) ]
      (.ok (burnTickUpdateLowerAfterFlippedFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolTickUpdateLowerSourceThroughMaxLiquidity
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hnonzero hdelta hle
  have htail :
      ExecBlock (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        [ .letDecl "flipped" (some boolTy)
            (neE (eqE (.var "liquidityGrossAfter") (.intLit 0))
              (eqE (.var "liquidityGrossBefore") (.intLit 0))) ]
        (.ok (burnTickUpdateLowerAfterFlippedFrame v σ I)
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (uniswapV3PoolTickUpdateLowerSourceFlippedStep
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g))
      ExecBlock.nil
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolTickUpdateLowerSourceThroughLiquidityGrossBeforeNonzero
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hdelta :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I)
    (hle :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick)
    (hbefore : burnTickUpdateLowerLiquidityGrossBeforeInt σ I ≠ 0) :
    ExecBlock (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "info" (ticksRef (.var "tick")),
        .letDecl "liquidityGrossBefore" (some uint128)
          (.field (.var "info") "liquidityGross"),
        .internalCall "liquidityAddDelta"
          [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter",
        .require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")),
        .letDecl "flipped" (some boolTy)
          (neE (eqE (.var "liquidityGrossAfter") (.intLit 0))
            (eqE (.var "liquidityGrossBefore") (.intLit 0))),
        Stmt.ite (eqE (.var "liquidityGrossBefore") (.intLit 0))
          [ Stmt.ite (leE (.var "tick") (.var "tickCurrent"))
              [ .assign .storage { base := "info", steps := [.field "feeGrowthOutside0X128"] }
                  (.var "feeGrowthGlobal0X128"),
                .assign .storage { base := "info", steps := [.field "feeGrowthOutside1X128"] }
                  (.var "feeGrowthGlobal1X128"),
                .assign .storage
                  { base := "info", steps := [.field "secondsPerLiquidityOutsideX128"] }
                  (.var "secondsPerLiquidityCumulativeX128"),
                .assign .storage { base := "info", steps := [.field "tickCumulativeOutside"] }
                  (.var "tickCumulative"),
                .assign .storage { base := "info", steps := [.field "secondsOutside"] }
                  (.var "time") ]
              [],
            .assign .storage { base := "info", steps := [.field "initialized"] } (.boolLit true) ]
          [] ]
      (.ok (burnTickUpdateLowerAfterFlippedFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolTickUpdateLowerSourceThroughFlipped
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hnonzero hdelta hle
  have htail :
      ExecBlock (config v) (burnTickUpdateLowerAfterFlippedFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        [ Stmt.ite (eqE (.var "liquidityGrossBefore") (.intLit 0))
            [ Stmt.ite (leE (.var "tick") (.var "tickCurrent"))
                [ .assign .storage
                    { base := "info", steps := [.field "feeGrowthOutside0X128"] }
                    (.var "feeGrowthGlobal0X128"),
                  .assign .storage
                    { base := "info", steps := [.field "feeGrowthOutside1X128"] }
                    (.var "feeGrowthGlobal1X128"),
                  .assign .storage
                    { base := "info", steps := [.field "secondsPerLiquidityOutsideX128"] }
                    (.var "secondsPerLiquidityCumulativeX128"),
                  .assign .storage
                    { base := "info", steps := [.field "tickCumulativeOutside"] }
                    (.var "tickCumulative"),
                  .assign .storage { base := "info", steps := [.field "secondsOutside"] }
                    (.var "time") ]
                [],
              .assign .storage { base := "info", steps := [.field "initialized"] }
                (.boolLit true) ]
            [] ]
        (.ok (burnTickUpdateLowerAfterFlippedFrame v σ I)
          (initState cA gh bl σ σ₀ g A I)) := by
    exact ExecBlock.consNormal
      (uniswapV3PoolTickUpdateLowerSourceLiquidityGrossBeforeNonzeroStep
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hbefore)
      ExecBlock.nil
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolTickUpdateLowerSourceMaxLiquidityRevertPrefix
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hdelta :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I)
    (hle :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick)
    (rest : List Stmt) :
    ExecBlock (config v) (burnTickUpdateLowerFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.letStorage "info" (ticksRef (.var "tick")) ::
        .letDecl "liquidityGrossBefore" (some uint128)
          (.field (.var "info") "liquidityGross") ::
        .internalCall "liquidityAddDelta"
          [.var "liquidityGrossBefore", .var "liquidityDelta"] "liquidityGrossAfter" ::
        .require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")) ::
        rest)
      .reverted := by
  have hprefix := uniswapV3PoolTickUpdateLowerSourceThroughLiquidityAddDeltaReturnPrefix
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hnonzero hdelta
  have htail :
      ExecBlock (config v) (burnTickUpdateLowerAfterLiquidityGrossAfterFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        (.require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")) :: rest)
        .reverted := by
    exact ExecBlock.consRevert
      (uniswapV3PoolTickUpdateLowerSourceMaxLiquidityRevertStep
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hle)
  simpa using execBlock_append hprefix htail

theorem uniswapV3PoolModifyPositionSourceLowerLiquidityAddDeltaReverts
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hbound : (slot0ObservationIndexWord σ I).toNat < 65535)
    (hsame :
      .int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat) =
        burnBlockTimestamp32Value I)
    (hreq :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolModifyPositionSourceThroughFeeGrowthGlobals (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge hle
  have htickBody :
      ExecFuncBody (config v) (burnTickUpdateLowerFrame v σ I)
        (initState cA gh bl σ σ₀ g A I) tickUpdateFunction.body .reverted := by
    refine ExecFuncBody.execBlockRevert ?_
    simpa [tickUpdateFunction] using
      uniswapV3PoolTickUpdateLowerSourceLiquidityAddDeltaRevertPrefix
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hnonzero hreq
        [ .require (leE (.var "liquidityGrossAfter") (.var "maxLiquidity")),
          .letDecl "flipped" (some boolTy)
            (neE (eqE (.var "liquidityGrossAfter") (.intLit 0))
              (eqE (.var "liquidityGrossBefore") (.intLit 0))),
          Stmt.ite (eqE (.var "liquidityGrossBefore") (.intLit 0))
            [ Stmt.ite (leE (.var "tick") (.var "tickCurrent"))
                [ .assign .storage { base := "info", steps := [.field "feeGrowthOutside0X128"] }
                    (.var "feeGrowthGlobal0X128"),
                  .assign .storage { base := "info", steps := [.field "feeGrowthOutside1X128"] }
                    (.var "feeGrowthGlobal1X128"),
                  .assign .storage
                    { base := "info", steps := [.field "secondsPerLiquidityOutsideX128"] }
                    (.var "secondsPerLiquidityCumulativeX128"),
                  .assign .storage { base := "info", steps := [.field "tickCumulativeOutside"] }
                    (.var "tickCumulative"),
                  .assign .storage { base := "info", steps := [.field "secondsOutside"] }
                    (.var "time") ]
                [],
              .assign .storage { base := "info", steps := [.field "initialized"] }
                (.boolLit true) ]
            [],
          .assign .storage { base := "info", steps := [.field "liquidityGross"] }
            (.var "liquidityGrossAfter"),
          .assign .storage { base := "info", steps := [.field "liquidityNet"] }
            (.inRange int128Int
              (.ite (.var "upper")
                (subE (.field (.var "info") "liquidityNet") (.var "liquidityDelta"))
                (addE (.field (.var "info") "liquidityNet") (.var "liquidityDelta")))),
          .return [.var "flipped"] ]
  have hstep :
      ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
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
      · refine ExecBlock.consNormal
          (uniswapV3PoolModifyPositionSourceObserveSingleTimestampEqualStep
            (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hbound hsame) ?_
        refine ExecBlock.consRevert ?_
        refine internalCallFunctionRevert (callee := tickUpdateFunction)
          (argVals := burnTickUpdateLowerArgValues v σ I)
          (locals := burnTickUpdateLowerStore v σ I) ?_ ?_ ?_ ?_
        · exact burnModifyPosition_evalLowerTickUpdateArgsAfterObserveSingle
            (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g)
        · simpa [burnModifyPositionAfterObserveSingleFrame] using
            uniswapV3PoolLookupTickUpdate v
        · exact burnTickUpdateLower_bindParams v σ I
        · exact htickBody
  have hmid := execBlock_append hprefix hstep
  have hfull := execBlock_append_term (s2 := burnModifyPositionAfterLiquidityDeltaTail v)
    hmid (by intro f e h; cases h)
  simpa [modifyPositionFunction, burnModifyPositionSlot0Prefix,
    burnModifyPositionPositionKeyStep, burnModifyPositionFeeGrowthGlobalsStep,
    burnModifyPositionLiquidityDeltaUpdateStep, burnModifyPositionAfterLiquidityDeltaTail]
    using hfull

theorem uniswapV3PoolBurnSourceLowerLiquidityAddDeltaReverts
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
    (hbound :
      (slot0ObservationIndexWord
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I).toNat < 65535)
    (hsame :
      .int (Int.ofNat (burnObserveSingleBlockTimestampWord
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I).toNat) =
        burnBlockTimestamp32Value I)
    (hreq :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I <
        burnTickUpdateLowerLiquidityGrossBeforeInt
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I) burnTransition.body .reverted := by
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
    · exact uniswapV3PoolModifyPositionSourceLowerLiquidityAddDeltaReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl)
        (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hguard htickLt hge hle hnonzero hbound hsame hreq
  simpa [burnTransition, nonpayable, lockPrefix] using
    execBlock_append hprefix (ExecBlock.consRevert hstmt)

theorem uniswapV3PoolModifyPositionSourceLowerMaxLiquidityReverts
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩)
    (hbound : (slot0ObservationIndexWord σ I).toNat < 65535)
    (hsame :
      .int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat) =
        burnBlockTimestamp32Value I)
    (hdelta :
      burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <
        burnTickUpdateLowerLiquidityGrossBeforeInt σ I)
    (hmax :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt σ I <= v.maxLiquidityPerTick) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolModifyPositionSourceThroughFeeGrowthGlobals (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge hle
  have htickBody :
      ExecFuncBody (config v) (burnTickUpdateLowerFrame v σ I)
        (initState cA gh bl σ σ₀ g A I) tickUpdateFunction.body .reverted := by
    refine ExecFuncBody.execBlockRevert ?_
    simpa [tickUpdateFunction] using
      uniswapV3PoolTickUpdateLowerSourceMaxLiquidityRevertPrefix
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
        (A := A) (I := I) (g := g) hnonzero hdelta hmax
        [ .letDecl "flipped" (some boolTy)
            (neE (eqE (.var "liquidityGrossAfter") (.intLit 0))
              (eqE (.var "liquidityGrossBefore") (.intLit 0))),
          Stmt.ite (eqE (.var "liquidityGrossBefore") (.intLit 0))
            [ Stmt.ite (leE (.var "tick") (.var "tickCurrent"))
                [ .assign .storage { base := "info", steps := [.field "feeGrowthOutside0X128"] }
                    (.var "feeGrowthGlobal0X128"),
                  .assign .storage { base := "info", steps := [.field "feeGrowthOutside1X128"] }
                    (.var "feeGrowthGlobal1X128"),
                  .assign .storage
                    { base := "info", steps := [.field "secondsPerLiquidityOutsideX128"] }
                    (.var "secondsPerLiquidityCumulativeX128"),
                  .assign .storage { base := "info", steps := [.field "tickCumulativeOutside"] }
                    (.var "tickCumulative"),
                  .assign .storage { base := "info", steps := [.field "secondsOutside"] }
                    (.var "time") ]
                [],
              .assign .storage { base := "info", steps := [.field "initialized"] }
                (.boolLit true) ]
            [],
          .assign .storage { base := "info", steps := [.field "liquidityGross"] }
            (.var "liquidityGrossAfter"),
          .assign .storage { base := "info", steps := [.field "liquidityNet"] }
            (.inRange int128Int
              (.ite (.var "upper")
                (subE (.field (.var "info") "liquidityNet") (.var "liquidityDelta"))
                (addE (.field (.var "info") "liquidityNet") (.var "liquidityDelta")))),
          .return [.var "flipped"] ]
  have hstep :
      ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
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
      · refine ExecBlock.consNormal
          (uniswapV3PoolModifyPositionSourceObserveSingleTimestampEqualStep
            (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g) hbound hsame) ?_
        refine ExecBlock.consRevert ?_
        refine internalCallFunctionRevert (callee := tickUpdateFunction)
          (argVals := burnTickUpdateLowerArgValues v σ I)
          (locals := burnTickUpdateLowerStore v σ I) ?_ ?_ ?_ ?_
        · exact burnModifyPosition_evalLowerTickUpdateArgsAfterObserveSingle
            (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
            (A := A) (I := I) (g := g)
        · simpa [burnModifyPositionAfterObserveSingleFrame] using
            uniswapV3PoolLookupTickUpdate v
        · exact burnTickUpdateLower_bindParams v σ I
        · exact htickBody
  have hmid := execBlock_append hprefix hstep
  have hfull := execBlock_append_term (s2 := burnModifyPositionAfterLiquidityDeltaTail v)
    hmid (by intro f e h; cases h)
  simpa [modifyPositionFunction, burnModifyPositionSlot0Prefix,
    burnModifyPositionPositionKeyStep, burnModifyPositionFeeGrowthGlobalsStep,
    burnModifyPositionLiquidityDeltaUpdateStep, burnModifyPositionAfterLiquidityDeltaTail]
    using hfull

theorem uniswapV3PoolBurnSourceLowerMaxLiquidityReverts
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
    (hbound :
      (slot0ObservationIndexWord
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I).toNat < 65535)
    (hsame :
      .int (Int.ofNat (burnObserveSingleBlockTimestampWord
        (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I).toNat) =
        burnBlockTimestamp32Value I)
    (hdelta :
      burnTickUpdateLowerLiquidityGrossAfterSubInt
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I <
        burnTickUpdateLowerLiquidityGrossBeforeInt
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I)
    (hmax :
      ¬ burnTickUpdateLowerLiquidityGrossAfterSubInt
          (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I)) I <=
        v.maxLiquidityPerTick) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (burnStore I) burnTransition.body .reverted := by
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
    · exact uniswapV3PoolModifyPositionSourceLowerMaxLiquidityReverts (v := v)
        (cA := cA) (gh := gh) (bl := bl)
        (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
        hguard htickLt hge hle hnonzero hbound hsame hdelta hmax
  simpa [burnTransition, nonpayable, lockPrefix] using
    execBlock_append hprefix (ExecBlock.consRevert hstmt)

end Benchmarks.UniswapV3Pool
