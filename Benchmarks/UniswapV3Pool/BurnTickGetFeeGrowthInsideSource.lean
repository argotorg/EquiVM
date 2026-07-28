import Benchmarks.UniswapV3Pool.BurnPositionUpdateSourceSuccess

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

theorem burnTickGet_evalCurrentGeLowerOf {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {frame : Frame}
    (hcurrent : frame.locals.get? "tickCurrent" = some (burnSlot0TickValue σ I))
    (hlower : frame.locals.get? "tickLower" = some (burnTickLowerValue I)) :
    evalExpr? (config v) frame (initState cA gh bl σ σ₀ g A I)
      (geE (.var "tickCurrent") (.var "tickLower")) =
        .ok (.bool (tickSpacingSint24Value (slot0TickRawWord σ I) >=
          tickSpacingSint24Value (burnTickLowerWord I))) := by
  simp only [geE, evalExpr?, EvalResult.bind, bind]
  rw [hcurrent, hlower]
  simp [EvalResult.ofOption, burnSlot0TickValue, burnTickLowerValue, wordToElem, int24Int,
    tickSpacingSint24Value, evalBinaryOp?]

theorem burnTickGet_evalCurrentLtUpperOf {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} {frame : Frame}
    (hcurrent : frame.locals.get? "tickCurrent" = some (burnSlot0TickValue σ I))
    (hupper : frame.locals.get? "tickUpper" = some (burnTickUpperValue I)) :
    evalExpr? (config v) frame (initState cA gh bl σ σ₀ g A I)
      (ltE (.var "tickCurrent") (.var "tickUpper")) =
        .ok (.bool (tickSpacingSint24Value (slot0TickRawWord σ I) <
          tickSpacingSint24Value (burnTickUpperWord I))) := by
  simp only [ltE, evalExpr?, EvalResult.bind, bind]
  rw [hcurrent, hupper]
  simp [EvalResult.ofOption, burnSlot0TickValue, burnTickUpperValue, wordToElem, int24Int,
    tickSpacingSint24Value, evalBinaryOp?]

theorem burnTickGetAfterUpper_feeGrowthGlobal0 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterUpperFrame v σ I).locals.get? "feeGrowthGlobal0X128" =
      some (burnFeeGrowthGlobal0Value σ I) := by
  rw [burnTickGetAfterUpperFrame, burnTickGetAfterLowerFrame]
  rw [store_get_ne (burnTickGetAfterLowerFrame v σ I).locals
    (k := "upper") (a := "feeGrowthGlobal0X128")
    (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  rw [store_get_ne (burnTickGetFeeGrowthInsideStore σ I)
    (k := "lower") (a := "feeGrowthGlobal0X128")
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  rw [burnTickGetFeeGrowthInsideStore]
  rw [store_get_ne3 ((∅ : Store)
    |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I)
    |>.insert "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
    (k1 := "tickCurrent") (k2 := "tickUpper") (k3 := "tickLower")
    (a := "feeGrowthGlobal0X128")
    (burnSlot0TickValue σ I) (burnTickUpperValue I) (burnTickLowerValue I)
    (by native_decide) (by native_decide) (by native_decide)]
  exact store_get_self ((∅ : Store)
    |>.insert "feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
    "feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I)

theorem burnTickGetAfterUpper_feeGrowthGlobal1 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterUpperFrame v σ I).locals.get? "feeGrowthGlobal1X128" =
      some (burnFeeGrowthGlobal1Value σ I) := by
  rw [burnTickGetAfterUpperFrame, burnTickGetAfterLowerFrame]
  rw [store_get_ne (burnTickGetAfterLowerFrame v σ I).locals
    (k := "upper") (a := "feeGrowthGlobal1X128")
    (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  rw [store_get_ne (burnTickGetFeeGrowthInsideStore σ I)
    (k := "lower") (a := "feeGrowthGlobal1X128")
    (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy)
    (by native_decide)]
  rw [burnTickGetFeeGrowthInsideStore]
  rw [store_get_ne4 ((∅ : Store).insert "feeGrowthGlobal1X128"
      (burnFeeGrowthGlobal1Value σ I))
    (k1 := "feeGrowthGlobal0X128") (k2 := "tickCurrent")
    (k3 := "tickUpper") (k4 := "tickLower") (a := "feeGrowthGlobal1X128")
    (burnFeeGrowthGlobal0Value σ I) (burnSlot0TickValue σ I)
    (burnTickUpperValue I) (burnTickLowerValue I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact store_get_self (∅ : Store) "feeGrowthGlobal1X128"
    (burnFeeGrowthGlobal1Value σ I)

theorem burnTickGetAfterBelow0_lower (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterBelow0Frame v σ I).locals.get? "lower" =
      some (.storageRef (burnTickGetLowerEvaledBaseRef I) tickInfoStructTy) := by
  rw [burnTickGetAfterBelow0Frame]
  rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
    (k := "feeGrowthBelow0X128") (a := "lower") (burnTickGetBelow0Value σ I)
    (by native_decide)]
  exact burnTickGetAfterUpper_lower v σ I

theorem burnTickGetAfterBelow0_tickCurrent (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterBelow0Frame v σ I).locals.get? "tickCurrent" =
      some (burnSlot0TickValue σ I) := by
  rw [burnTickGetAfterBelow0Frame]
  rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
    (k := "feeGrowthBelow0X128") (a := "tickCurrent") (burnTickGetBelow0Value σ I)
    (by native_decide)]
  exact burnTickGetAfterUpper_tickCurrent v σ I

theorem burnTickGetAfterBelow0_tickLower (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterBelow0Frame v σ I).locals.get? "tickLower" =
      some (burnTickLowerValue I) := by
  rw [burnTickGetAfterBelow0Frame]
  rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
    (k := "feeGrowthBelow0X128") (a := "tickLower") (burnTickGetBelow0Value σ I)
    (by native_decide)]
  exact burnTickGetAfterUpper_tickLower v σ I

theorem burnTickGetAfterBelow0_feeGrowthGlobal1 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterBelow0Frame v σ I).locals.get? "feeGrowthGlobal1X128" =
      some (burnFeeGrowthGlobal1Value σ I) := by
  rw [burnTickGetAfterBelow0Frame]
  rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
    (k := "feeGrowthBelow0X128") (a := "feeGrowthGlobal1X128")
    (burnTickGetBelow0Value σ I) (by native_decide)]
  exact burnTickGetAfterUpper_feeGrowthGlobal1 v σ I

theorem burnTickGetAfterBelow1_upper (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterBelow1Frame v σ I).locals.get? "upper" =
      some (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy) := by
  rw [burnTickGetAfterBelow1Frame, burnTickGetAfterBelow0Frame]
  rw [store_get_ne (burnTickGetAfterBelow0Frame v σ I).locals
    (k := "feeGrowthBelow1X128") (a := "upper") (burnTickGetBelow1Value σ I)
    (by native_decide)]
  rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
    (k := "feeGrowthBelow0X128") (a := "upper") (burnTickGetBelow0Value σ I)
    (by native_decide)]
  exact burnTickGetAfterUpper_upper v σ I

theorem burnTickGetAfterBelow1_tickCurrent (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterBelow1Frame v σ I).locals.get? "tickCurrent" =
      some (burnSlot0TickValue σ I) := by
  rw [burnTickGetAfterBelow1Frame]
  rw [store_get_ne (burnTickGetAfterBelow0Frame v σ I).locals
    (k := "feeGrowthBelow1X128") (a := "tickCurrent") (burnTickGetBelow1Value σ I)
    (by native_decide)]
  exact burnTickGetAfterBelow0_tickCurrent v σ I

theorem burnTickGetAfterBelow1_tickUpper (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterBelow1Frame v σ I).locals.get? "tickUpper" =
      some (burnTickUpperValue I) := by
  rw [burnTickGetAfterBelow1Frame, burnTickGetAfterBelow0Frame]
  rw [store_get_ne (burnTickGetAfterBelow0Frame v σ I).locals
    (k := "feeGrowthBelow1X128") (a := "tickUpper") (burnTickGetBelow1Value σ I)
    (by native_decide)]
  rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
    (k := "feeGrowthBelow0X128") (a := "tickUpper") (burnTickGetBelow0Value σ I)
    (by native_decide)]
  exact burnTickGetAfterUpper_tickUpper v σ I

theorem burnTickGetAfterBelow1_feeGrowthGlobal0 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterBelow1Frame v σ I).locals.get? "feeGrowthGlobal0X128" =
      some (burnFeeGrowthGlobal0Value σ I) := by
  rw [burnTickGetAfterBelow1Frame, burnTickGetAfterBelow0Frame]
  rw [store_get_ne (burnTickGetAfterBelow0Frame v σ I).locals
    (k := "feeGrowthBelow1X128") (a := "feeGrowthGlobal0X128")
    (burnTickGetBelow1Value σ I) (by native_decide)]
  rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
    (k := "feeGrowthBelow0X128") (a := "feeGrowthGlobal0X128")
    (burnTickGetBelow0Value σ I) (by native_decide)]
  exact burnTickGetAfterUpper_feeGrowthGlobal0 v σ I

theorem burnTickGetAfterAbove0_upper (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove0Frame v σ I).locals.get? "upper" =
      some (.storageRef (burnTickGetUpperEvaledBaseRef I) tickInfoStructTy) := by
  rw [burnTickGetAfterAbove0Frame]
  rw [store_get_ne (burnTickGetAfterBelow1Frame v σ I).locals
    (k := "feeGrowthAbove0X128") (a := "upper") (burnTickGetAbove0Value σ I)
    (by native_decide)]
  exact burnTickGetAfterBelow1_upper v σ I

theorem burnTickGetAfterAbove0_tickCurrent (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove0Frame v σ I).locals.get? "tickCurrent" =
      some (burnSlot0TickValue σ I) := by
  rw [burnTickGetAfterAbove0Frame]
  rw [store_get_ne (burnTickGetAfterBelow1Frame v σ I).locals
    (k := "feeGrowthAbove0X128") (a := "tickCurrent") (burnTickGetAbove0Value σ I)
    (by native_decide)]
  exact burnTickGetAfterBelow1_tickCurrent v σ I

theorem burnTickGetAfterAbove0_tickUpper (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove0Frame v σ I).locals.get? "tickUpper" =
      some (burnTickUpperValue I) := by
  rw [burnTickGetAfterAbove0Frame]
  rw [store_get_ne (burnTickGetAfterBelow1Frame v σ I).locals
    (k := "feeGrowthAbove0X128") (a := "tickUpper") (burnTickGetAbove0Value σ I)
    (by native_decide)]
  exact burnTickGetAfterBelow1_tickUpper v σ I

theorem burnTickGetAfterAbove0_feeGrowthGlobal1 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove0Frame v σ I).locals.get? "feeGrowthGlobal1X128" =
      some (burnFeeGrowthGlobal1Value σ I) := by
  rw [burnTickGetAfterAbove0Frame, burnTickGetAfterBelow1Frame, burnTickGetAfterBelow0Frame]
  rw [store_get_ne (burnTickGetAfterBelow1Frame v σ I).locals
    (k := "feeGrowthAbove0X128") (a := "feeGrowthGlobal1X128")
    (burnTickGetAbove0Value σ I) (by native_decide)]
  rw [store_get_ne (burnTickGetAfterBelow0Frame v σ I).locals
    (k := "feeGrowthBelow1X128") (a := "feeGrowthGlobal1X128")
    (burnTickGetBelow1Value σ I) (by native_decide)]
  rw [store_get_ne (burnTickGetAfterUpperFrame v σ I).locals
    (k := "feeGrowthBelow0X128") (a := "feeGrowthGlobal1X128")
    (burnTickGetBelow0Value σ I) (by native_decide)]
  exact burnTickGetAfterUpper_feeGrowthGlobal1 v σ I

theorem burnTickGet_evalFeeGrowthBelow0 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnTickGetAfterUpperFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.ite (geE (.var "tickCurrent") (.var "tickLower"))
        (.field (.var "lower") "feeGrowthOutside0X128")
        (wordSub (.var "feeGrowthGlobal0X128")
          (.field (.var "lower") "feeGrowthOutside0X128"))) =
        .ok (burnTickGetBelow0Value σ I) := by
  rw [evalExpr?, burnTickGet_evalCurrentGeLower]
  by_cases hge : tickSpacingSint24Value (slot0TickRawWord σ I) >=
      tickSpacingSint24Value (burnTickLowerWord I)
  · simp [hge]
    simpa [burnTickGetBelow0Value, burnTickGetBelow0Int, hge] using
      burnTickGet_evalLowerFeeGrowthOutside0 (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (frame := burnTickGetAfterUpperFrame v σ I) (burnTickGetAfterUpper_lower v σ I)
  · simp [hge]
    apply Eq.trans
    · refine evalExpr_wordSub_int (v := v) (frame := burnTickGetAfterUpperFrame v σ I)
        (evm := initState cA gh bl σ σ₀ g A I)
        (x := burnTickGetFeeGrowthGlobal0Int σ I)
        (y := burnTickGetLowerFeeGrowthOutside0Int σ I) ?_ ?_
      · simp only [evalExpr?]
        rw [burnTickGetAfterUpper_feeGrowthGlobal0 v σ I]
        simp [EvalResult.ofOption, burnFeeGrowthGlobal0Value, burnTickGetFeeGrowthGlobal0Int]
      · exact burnTickGet_evalLowerFeeGrowthOutside0 (v := v) (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (frame := burnTickGetAfterUpperFrame v σ I) (burnTickGetAfterUpper_lower v σ I)
    · simp [burnTickGetBelow0Value, burnTickGetBelow0Int, hge,
        burnTickGetFeeGrowthGlobal0Int, burnTickGetLowerFeeGrowthOutside0Int]

theorem burnTickGet_evalFeeGrowthBelow1 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnTickGetAfterBelow0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.ite (geE (.var "tickCurrent") (.var "tickLower"))
        (.field (.var "lower") "feeGrowthOutside1X128")
        (wordSub (.var "feeGrowthGlobal1X128")
          (.field (.var "lower") "feeGrowthOutside1X128"))) =
        .ok (burnTickGetBelow1Value σ I) := by
  rw [evalExpr?]
  rw [burnTickGet_evalCurrentGeLowerOf
    (frame := burnTickGetAfterBelow0Frame v σ I)
    (burnTickGetAfterBelow0_tickCurrent v σ I)
    (burnTickGetAfterBelow0_tickLower v σ I)]
  by_cases hge : tickSpacingSint24Value (slot0TickRawWord σ I) >=
      tickSpacingSint24Value (burnTickLowerWord I)
  · simp [hge]
    simpa [burnTickGetBelow1Value, burnTickGetBelow1Int, hge] using
      burnTickGet_evalLowerFeeGrowthOutside1 (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (frame := burnTickGetAfterBelow0Frame v σ I) (burnTickGetAfterBelow0_lower v σ I)
  · simp [hge]
    apply Eq.trans
    · refine evalExpr_wordSub_int (v := v) (frame := burnTickGetAfterBelow0Frame v σ I)
        (evm := initState cA gh bl σ σ₀ g A I)
        (x := burnTickGetFeeGrowthGlobal1Int σ I)
        (y := burnTickGetLowerFeeGrowthOutside1Int σ I) ?_ ?_
      · simp only [evalExpr?]
        rw [burnTickGetAfterBelow0_feeGrowthGlobal1 v σ I]
        simp [EvalResult.ofOption, burnFeeGrowthGlobal1Value, burnTickGetFeeGrowthGlobal1Int]
      · exact burnTickGet_evalLowerFeeGrowthOutside1 (v := v) (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (frame := burnTickGetAfterBelow0Frame v σ I) (burnTickGetAfterBelow0_lower v σ I)
    · simp [burnTickGetBelow1Value, burnTickGetBelow1Int, hge,
        burnTickGetFeeGrowthGlobal1Int, burnTickGetLowerFeeGrowthOutside1Int]

theorem burnTickGet_evalFeeGrowthAbove0 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnTickGetAfterBelow1Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.ite (ltE (.var "tickCurrent") (.var "tickUpper"))
        (.field (.var "upper") "feeGrowthOutside0X128")
        (wordSub (.var "feeGrowthGlobal0X128")
          (.field (.var "upper") "feeGrowthOutside0X128"))) =
        .ok (burnTickGetAbove0Value σ I) := by
  rw [evalExpr?]
  rw [burnTickGet_evalCurrentLtUpperOf
    (frame := burnTickGetAfterBelow1Frame v σ I)
    (burnTickGetAfterBelow1_tickCurrent v σ I)
    (burnTickGetAfterBelow1_tickUpper v σ I)]
  by_cases hlt : tickSpacingSint24Value (slot0TickRawWord σ I) <
      tickSpacingSint24Value (burnTickUpperWord I)
  · simp [hlt]
    simpa [burnTickGetAbove0Value, burnTickGetAbove0Int, hlt] using
      burnTickGet_evalUpperFeeGrowthOutside0 (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (frame := burnTickGetAfterBelow1Frame v σ I) (burnTickGetAfterBelow1_upper v σ I)
  · simp [hlt]
    apply Eq.trans
    · refine evalExpr_wordSub_int (v := v) (frame := burnTickGetAfterBelow1Frame v σ I)
        (evm := initState cA gh bl σ σ₀ g A I)
        (x := burnTickGetFeeGrowthGlobal0Int σ I)
        (y := burnTickGetUpperFeeGrowthOutside0Int σ I) ?_ ?_
      · simp only [evalExpr?]
        rw [burnTickGetAfterBelow1_feeGrowthGlobal0 v σ I]
        simp [EvalResult.ofOption, burnFeeGrowthGlobal0Value, burnTickGetFeeGrowthGlobal0Int]
      · exact burnTickGet_evalUpperFeeGrowthOutside0 (v := v) (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (frame := burnTickGetAfterBelow1Frame v σ I) (burnTickGetAfterBelow1_upper v σ I)
    · simp [burnTickGetAbove0Value, burnTickGetAbove0Int, hlt,
        burnTickGetFeeGrowthGlobal0Int, burnTickGetUpperFeeGrowthOutside0Int]

theorem burnTickGet_evalFeeGrowthAbove1 {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnTickGetAfterAbove0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.ite (ltE (.var "tickCurrent") (.var "tickUpper"))
        (.field (.var "upper") "feeGrowthOutside1X128")
        (wordSub (.var "feeGrowthGlobal1X128")
          (.field (.var "upper") "feeGrowthOutside1X128"))) =
        .ok (burnTickGetAbove1Value σ I) := by
  rw [evalExpr?]
  rw [burnTickGet_evalCurrentLtUpperOf
    (frame := burnTickGetAfterAbove0Frame v σ I)
    (burnTickGetAfterAbove0_tickCurrent v σ I)
    (burnTickGetAfterAbove0_tickUpper v σ I)]
  by_cases hlt : tickSpacingSint24Value (slot0TickRawWord σ I) <
      tickSpacingSint24Value (burnTickUpperWord I)
  · simp [hlt]
    simpa [burnTickGetAbove1Value, burnTickGetAbove1Int, hlt] using
      burnTickGet_evalUpperFeeGrowthOutside1 (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
        (frame := burnTickGetAfterAbove0Frame v σ I) (burnTickGetAfterAbove0_upper v σ I)
  · simp [hlt]
    apply Eq.trans
    · refine evalExpr_wordSub_int (v := v) (frame := burnTickGetAfterAbove0Frame v σ I)
        (evm := initState cA gh bl σ σ₀ g A I)
        (x := burnTickGetFeeGrowthGlobal1Int σ I)
        (y := burnTickGetUpperFeeGrowthOutside1Int σ I) ?_ ?_
      · simp only [evalExpr?]
        rw [burnTickGetAfterAbove0_feeGrowthGlobal1 v σ I]
        simp [EvalResult.ofOption, burnFeeGrowthGlobal1Value, burnTickGetFeeGrowthGlobal1Int]
      · exact burnTickGet_evalUpperFeeGrowthOutside1 (v := v) (cA := cA) (gh := gh)
          (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
          (frame := burnTickGetAfterAbove0Frame v σ I) (burnTickGetAfterAbove0_upper v σ I)
    · simp [burnTickGetAbove1Value, burnTickGetAbove1Int, hlt,
        burnTickGetFeeGrowthGlobal1Int, burnTickGetUpperFeeGrowthOutside1Int]

theorem burnTickGetAfterAbove0_feeGrowthGlobal0 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove0Frame v σ I).locals.get? "feeGrowthGlobal0X128" =
      some (burnFeeGrowthGlobal0Value σ I) := by
  rw [burnTickGetAfterAbove0Frame]
  rw [store_get_ne (burnTickGetAfterBelow1Frame v σ I).locals
    (k := "feeGrowthAbove0X128") (a := "feeGrowthGlobal0X128")
    (burnTickGetAbove0Value σ I) (by native_decide)]
  exact burnTickGetAfterBelow1_feeGrowthGlobal0 v σ I

theorem burnTickGetAfterAbove1_feeGrowthGlobal0 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove1Frame v σ I).locals.get? "feeGrowthGlobal0X128" =
      some (burnFeeGrowthGlobal0Value σ I) := by
  rw [burnTickGetAfterAbove1Frame]
  rw [store_get_ne (burnTickGetAfterAbove0Frame v σ I).locals
    (k := "feeGrowthAbove1X128") (a := "feeGrowthGlobal0X128")
    (burnTickGetAbove1Value σ I) (by native_decide)]
  exact burnTickGetAfterAbove0_feeGrowthGlobal0 v σ I

theorem burnTickGetAfterAbove1_feeGrowthGlobal1 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove1Frame v σ I).locals.get? "feeGrowthGlobal1X128" =
      some (burnFeeGrowthGlobal1Value σ I) := by
  rw [burnTickGetAfterAbove1Frame]
  rw [store_get_ne (burnTickGetAfterAbove0Frame v σ I).locals
    (k := "feeGrowthAbove1X128") (a := "feeGrowthGlobal1X128")
    (burnTickGetAbove1Value σ I) (by native_decide)]
  exact burnTickGetAfterAbove0_feeGrowthGlobal1 v σ I

theorem burnTickGetAfterAbove1_below0 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove1Frame v σ I).locals.get? "feeGrowthBelow0X128" =
      some (burnTickGetBelow0Value σ I) := by
  rw [burnTickGetAfterAbove1Frame, burnTickGetAfterAbove0Frame,
    burnTickGetAfterBelow1Frame]
  rw [store_get_ne (burnTickGetAfterAbove0Frame v σ I).locals
    (k := "feeGrowthAbove1X128") (a := "feeGrowthBelow0X128")
    (burnTickGetAbove1Value σ I) (by native_decide)]
  rw [store_get_ne (burnTickGetAfterBelow1Frame v σ I).locals
    (k := "feeGrowthAbove0X128") (a := "feeGrowthBelow0X128")
    (burnTickGetAbove0Value σ I) (by native_decide)]
  rw [store_get_ne (burnTickGetAfterBelow0Frame v σ I).locals
    (k := "feeGrowthBelow1X128") (a := "feeGrowthBelow0X128")
    (burnTickGetBelow1Value σ I) (by native_decide)]
  rw [burnTickGetAfterBelow0Frame]
  exact store_get_self (burnTickGetAfterUpperFrame v σ I).locals
    "feeGrowthBelow0X128" (burnTickGetBelow0Value σ I)

theorem burnTickGetAfterAbove1_below1 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove1Frame v σ I).locals.get? "feeGrowthBelow1X128" =
      some (burnTickGetBelow1Value σ I) := by
  rw [burnTickGetAfterAbove1Frame, burnTickGetAfterAbove0Frame]
  rw [store_get_ne (burnTickGetAfterAbove0Frame v σ I).locals
    (k := "feeGrowthAbove1X128") (a := "feeGrowthBelow1X128")
    (burnTickGetAbove1Value σ I) (by native_decide)]
  rw [store_get_ne (burnTickGetAfterBelow1Frame v σ I).locals
    (k := "feeGrowthAbove0X128") (a := "feeGrowthBelow1X128")
    (burnTickGetAbove0Value σ I) (by native_decide)]
  rw [burnTickGetAfterBelow1Frame]
  exact store_get_self (burnTickGetAfterBelow0Frame v σ I).locals
    "feeGrowthBelow1X128" (burnTickGetBelow1Value σ I)

theorem burnTickGetAfterAbove1_above0 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove1Frame v σ I).locals.get? "feeGrowthAbove0X128" =
      some (burnTickGetAbove0Value σ I) := by
  rw [burnTickGetAfterAbove1Frame]
  rw [store_get_ne (burnTickGetAfterAbove0Frame v σ I).locals
    (k := "feeGrowthAbove1X128") (a := "feeGrowthAbove0X128")
    (burnTickGetAbove1Value σ I) (by native_decide)]
  rw [burnTickGetAfterAbove0Frame]
  exact store_get_self (burnTickGetAfterBelow1Frame v σ I).locals
    "feeGrowthAbove0X128" (burnTickGetAbove0Value σ I)

theorem burnTickGetAfterAbove1_above1 (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnTickGetAfterAbove1Frame v σ I).locals.get? "feeGrowthAbove1X128" =
      some (burnTickGetAbove1Value σ I) := by
  rw [burnTickGetAfterAbove1Frame]
  exact store_get_self (burnTickGetAfterAbove0Frame v σ I).locals
    "feeGrowthAbove1X128" (burnTickGetAbove1Value σ I)

theorem burnTickGet_evalReturnValues {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExprs? (config v) (burnTickGetAfterAbove1Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ wordSub (wordSub (.var "feeGrowthGlobal0X128") (.var "feeGrowthBelow0X128"))
          (.var "feeGrowthAbove0X128"),
        wordSub (wordSub (.var "feeGrowthGlobal1X128") (.var "feeGrowthBelow1X128"))
          (.var "feeGrowthAbove1X128") ] =
        .ok [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I] := by
  have hglobal0 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthGlobal0X128") =
        .ok (.int (burnTickGetFeeGrowthGlobal0Int σ I)) := by
    simp only [evalExpr?]
    rw [burnTickGetAfterAbove1_feeGrowthGlobal0 v σ I]
    simp [EvalResult.ofOption, burnFeeGrowthGlobal0Value, burnTickGetFeeGrowthGlobal0Int]
  have hglobal1 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthGlobal1X128") =
        .ok (.int (burnTickGetFeeGrowthGlobal1Int σ I)) := by
    simp only [evalExpr?]
    rw [burnTickGetAfterAbove1_feeGrowthGlobal1 v σ I]
    simp [EvalResult.ofOption, burnFeeGrowthGlobal1Value, burnTickGetFeeGrowthGlobal1Int]
  have hbelow0 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthBelow0X128") =
        .ok (.int (burnTickGetBelow0Int σ I)) := by
    simp only [evalExpr?]
    rw [burnTickGetAfterAbove1_below0 v σ I]
    simp [EvalResult.ofOption, burnTickGetBelow0Value]
  have hbelow1 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthBelow1X128") =
        .ok (.int (burnTickGetBelow1Int σ I)) := by
    simp only [evalExpr?]
    rw [burnTickGetAfterAbove1_below1 v σ I]
    simp [EvalResult.ofOption, burnTickGetBelow1Value]
  have habove0 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthAbove0X128") =
        .ok (.int (burnTickGetAbove0Int σ I)) := by
    simp only [evalExpr?]
    rw [burnTickGetAfterAbove1_above0 v σ I]
    simp [EvalResult.ofOption, burnTickGetAbove0Value]
  have habove1 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I) (.var "feeGrowthAbove1X128") =
        .ok (.int (burnTickGetAbove1Int σ I)) := by
    simp only [evalExpr?]
    rw [burnTickGetAfterAbove1_above1 v σ I]
    simp [EvalResult.ofOption, burnTickGetAbove1Value]
  have hinner0 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        (wordSub (.var "feeGrowthGlobal0X128") (.var "feeGrowthBelow0X128")) =
          .ok (.int
            (burnWordSubInt (burnTickGetFeeGrowthGlobal0Int σ I)
              (burnTickGetBelow0Int σ I))) := by
    exact evalExpr_wordSub_int (v := v) (frame := burnTickGetAfterAbove1Frame v σ I)
      (evm := initState cA gh bl σ σ₀ g A I) hglobal0 hbelow0
  have hinner1 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        (wordSub (.var "feeGrowthGlobal1X128") (.var "feeGrowthBelow1X128")) =
          .ok (.int
            (burnWordSubInt (burnTickGetFeeGrowthGlobal1Int σ I)
              (burnTickGetBelow1Int σ I))) := by
    exact evalExpr_wordSub_int (v := v) (frame := burnTickGetAfterAbove1Frame v σ I)
      (evm := initState cA gh bl σ σ₀ g A I) hglobal1 hbelow1
  have hret0 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        (wordSub (wordSub (.var "feeGrowthGlobal0X128") (.var "feeGrowthBelow0X128"))
          (.var "feeGrowthAbove0X128")) =
          .ok (burnTickGetInside0Value σ I) := by
    simpa [burnTickGetInside0Value, burnTickGetInside0Int] using
      evalExpr_wordSub_int (v := v) (frame := burnTickGetAfterAbove1Frame v σ I)
        (evm := initState cA gh bl σ σ₀ g A I) hinner0 habove0
  have hret1 :
      evalExpr? (config v) (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        (wordSub (wordSub (.var "feeGrowthGlobal1X128") (.var "feeGrowthBelow1X128"))
          (.var "feeGrowthAbove1X128")) =
          .ok (burnTickGetInside1Value σ I) := by
    simpa [burnTickGetInside1Value, burnTickGetInside1Int] using
      evalExpr_wordSub_int (v := v) (frame := burnTickGetAfterAbove1Frame v σ I)
        (evm := initState cA gh bl σ σ₀ g A I) hinner1 habove1
  simp only [evalExprs?, hret0, hret1, EvalResult.bind, bind, pure]

theorem uniswapV3PoolTickGetFeeGrowthInsideSourceReturns {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecFuncBody (config v) (burnTickGetFeeGrowthInsideFrame v σ I)
      (initState cA gh bl σ σ₀ g A I) tickGetFeeGrowthInsideFunction.body
      (.returned (burnTickGetAfterAbove1Frame v σ I)
        (initState cA gh bl σ σ₀ g A I)
        (some [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I])) := by
  change ExecFuncBody (config v) (burnTickGetFeeGrowthInsideFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .letStorage "lower" (ticksRef (.var "tickLower")),
        .letStorage "upper" (ticksRef (.var "tickUpper")),
        .letDecl "feeGrowthBelow0X128" (some uint256)
          (.ite (geE (.var "tickCurrent") (.var "tickLower"))
            (.field (.var "lower") "feeGrowthOutside0X128")
            (wordSub (.var "feeGrowthGlobal0X128")
              (.field (.var "lower") "feeGrowthOutside0X128"))),
        .letDecl "feeGrowthBelow1X128" (some uint256)
          (.ite (geE (.var "tickCurrent") (.var "tickLower"))
            (.field (.var "lower") "feeGrowthOutside1X128")
            (wordSub (.var "feeGrowthGlobal1X128")
              (.field (.var "lower") "feeGrowthOutside1X128"))),
        .letDecl "feeGrowthAbove0X128" (some uint256)
          (.ite (ltE (.var "tickCurrent") (.var "tickUpper"))
            (.field (.var "upper") "feeGrowthOutside0X128")
            (wordSub (.var "feeGrowthGlobal0X128")
              (.field (.var "upper") "feeGrowthOutside0X128"))),
        .letDecl "feeGrowthAbove1X128" (some uint256)
          (.ite (ltE (.var "tickCurrent") (.var "tickUpper"))
            (.field (.var "upper") "feeGrowthOutside1X128")
            (wordSub (.var "feeGrowthGlobal1X128")
              (.field (.var "upper") "feeGrowthOutside1X128"))),
        .return
          [ wordSub (wordSub (.var "feeGrowthGlobal0X128") (.var "feeGrowthBelow0X128"))
              (.var "feeGrowthAbove0X128"),
            wordSub (wordSub (.var "feeGrowthGlobal1X128") (.var "feeGrowthBelow1X128"))
              (.var "feeGrowthAbove1X128") ] ] _
  refine ExecFuncBody.execBlockRet ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (burnTickGet_resolveLowerRef
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g))) ?_
  refine ExecBlock.consNormal (ExecStmt.letStorage (burnTickGetAfterLower_resolveUpperRef
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (burnTickGet_evalFeeGrowthBelow0
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (burnTickGet_evalFeeGrowthBelow1
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (burnTickGet_evalFeeGrowthAbove0
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (burnTickGet_evalFeeGrowthAbove1
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g))) ?_
  exact ExecBlock.consReturn (ExecStmt.return (burnTickGet_evalReturnValues
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g)))

def burnModifyPositionAfterLiquidityDeltaTail (_v : PoolImmutables) : List Stmt :=
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

abbrev burnModifyPositionAfterFeeGrowthInsideFrame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.insert
      "feeGrowthInside" (.tuple [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I]) }

theorem burnAfterSlot0Frame_slot0tick {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterSlot0Frame v σ I).locals.get? "_slot0tick" =
      some (burnSlot0TickValue σ I) := by
  rw [burnModifyPositionAfterSlot0Frame]
  rw [store_get_ne3
    ((burnModifyPositionStore I).insert "_slot0sqrtPriceX96"
      (burnSlot0SqrtPriceX96Value σ I) |>.insert "_slot0tick" (burnSlot0TickValue σ I))
    (k1 := "_slot0observationIndex") (k2 := "_slot0observationCardinality")
    (k3 := "_slot0observationCardinalityNext") (a := "_slot0tick")
    (burnSlot0ObservationIndexValue σ I) (burnSlot0ObservationCardinalityValue σ I)
    (burnSlot0ObservationCardinalityNextValue σ I)
    (by native_decide) (by native_decide) (by native_decide)]
  exact store_get_self
    ((burnModifyPositionStore I).insert "_slot0sqrtPriceX96"
      (burnSlot0SqrtPriceX96Value σ I))
    "_slot0tick" (burnSlot0TickValue σ I)

theorem burnAfterPositionKeyFrame_tickLower {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterPositionKeyFrame v σ I).locals.get? "tickLower" =
      some (burnTickLowerValue I) := by
  rw [burnModifyPositionAfterPositionKeyFrame]
  rw [store_get_ne (burnModifyPositionAfterSlot0Frame v σ I).locals
    (k := "_positionKey") (a := "tickLower") (burnPositionKeyValue I)
    (by native_decide)]
  exact burnAfterSlot0Frame_tickLower σ I

theorem burnAfterPositionKeyFrame_tickUpper {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterPositionKeyFrame v σ I).locals.get? "tickUpper" =
      some (burnTickUpperValue I) := by
  rw [burnModifyPositionAfterPositionKeyFrame]
  rw [store_get_ne (burnModifyPositionAfterSlot0Frame v σ I).locals
    (k := "_positionKey") (a := "tickUpper") (burnPositionKeyValue I)
    (by native_decide)]
  exact burnAfterSlot0Frame_tickUpper σ I

theorem burnAfterPositionKeyFrame_slot0tick {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterPositionKeyFrame v σ I).locals.get? "_slot0tick" =
      some (burnSlot0TickValue σ I) := by
  rw [burnModifyPositionAfterPositionKeyFrame]
  rw [store_get_ne (burnModifyPositionAfterSlot0Frame v σ I).locals
    (k := "_positionKey") (a := "_slot0tick") (burnPositionKeyValue I)
    (by native_decide)]
  exact burnAfterSlot0Frame_slot0tick σ I

theorem burnAfterPositionKeyFrame_positionKey {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterPositionKeyFrame v σ I).locals.get? "_positionKey" =
      some (burnPositionKeyValue I) := by
  rw [burnModifyPositionAfterPositionKeyFrame]
  exact store_get_self (burnModifyPositionAfterSlot0Frame v σ I).locals
    "_positionKey" (burnPositionKeyValue I)

theorem burnAfterFeeGrowthGlobalsFrame_tickLower {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.get? "tickLower" =
      some (burnTickLowerValue I) := by
  rw [burnModifyPositionAfterFeeGrowthGlobalsFrame]
  rw [store_get_ne4 (burnModifyPositionAfterPositionKeyFrame v σ I).locals
    (k1 := "_feeGrowthGlobal0X128") (k2 := "_feeGrowthGlobal1X128")
    (k3 := "flippedLower") (k4 := "flippedUpper") (a := "tickLower")
    (burnFeeGrowthGlobal0Value σ I) (burnFeeGrowthGlobal1Value σ I)
    (.bool false) (.bool false)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact burnAfterPositionKeyFrame_tickLower σ I

theorem burnAfterFeeGrowthGlobalsFrame_tickUpper {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.get? "tickUpper" =
      some (burnTickUpperValue I) := by
  rw [burnModifyPositionAfterFeeGrowthGlobalsFrame]
  rw [store_get_ne4 (burnModifyPositionAfterPositionKeyFrame v σ I).locals
    (k1 := "_feeGrowthGlobal0X128") (k2 := "_feeGrowthGlobal1X128")
    (k3 := "flippedLower") (k4 := "flippedUpper") (a := "tickUpper")
    (burnFeeGrowthGlobal0Value σ I) (burnFeeGrowthGlobal1Value σ I)
    (.bool false) (.bool false)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact burnAfterPositionKeyFrame_tickUpper σ I

theorem burnAfterFeeGrowthGlobalsFrame_slot0tick {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.get? "_slot0tick" =
      some (burnSlot0TickValue σ I) := by
  rw [burnModifyPositionAfterFeeGrowthGlobalsFrame]
  rw [store_get_ne4 (burnModifyPositionAfterPositionKeyFrame v σ I).locals
    (k1 := "_feeGrowthGlobal0X128") (k2 := "_feeGrowthGlobal1X128")
    (k3 := "flippedLower") (k4 := "flippedUpper") (a := "_slot0tick")
    (burnFeeGrowthGlobal0Value σ I) (burnFeeGrowthGlobal1Value σ I)
    (.bool false) (.bool false)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact burnAfterPositionKeyFrame_slot0tick σ I

theorem burnAfterFeeGrowthGlobalsFrame_positionKey {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.get? "_positionKey" =
      some (burnPositionKeyValue I) := by
  rw [burnModifyPositionAfterFeeGrowthGlobalsFrame]
  rw [store_get_ne4 (burnModifyPositionAfterPositionKeyFrame v σ I).locals
    (k1 := "_feeGrowthGlobal0X128") (k2 := "_feeGrowthGlobal1X128")
    (k3 := "flippedLower") (k4 := "flippedUpper") (a := "_positionKey")
    (burnFeeGrowthGlobal0Value σ I) (burnFeeGrowthGlobal1Value σ I)
    (.bool false) (.bool false)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact burnAfterPositionKeyFrame_positionKey σ I

theorem burnAfterFeeGrowthGlobalsFrame_feeGrowthGlobal0 {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.get?
      "_feeGrowthGlobal0X128" = some (burnFeeGrowthGlobal0Value σ I) := by
  rw [burnModifyPositionAfterFeeGrowthGlobalsFrame]
  rw [store_get_ne3
    ((burnModifyPositionAfterPositionKeyFrame v σ I).locals.insert
      "_feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
    (k1 := "_feeGrowthGlobal1X128") (k2 := "flippedLower") (k3 := "flippedUpper")
    (a := "_feeGrowthGlobal0X128") (burnFeeGrowthGlobal1Value σ I)
    (.bool false) (.bool false)
    (by native_decide) (by native_decide) (by native_decide)]
  exact store_get_self (burnModifyPositionAfterPositionKeyFrame v σ I).locals
    "_feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I)

theorem burnAfterFeeGrowthGlobalsFrame_feeGrowthGlobal1 {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.get?
      "_feeGrowthGlobal1X128" = some (burnFeeGrowthGlobal1Value σ I) := by
  rw [burnModifyPositionAfterFeeGrowthGlobalsFrame]
  rw [store_get_ne2
    ((burnModifyPositionAfterPositionKeyFrame v σ I).locals.insert
      "_feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I)
      |>.insert "_feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
    (k1 := "flippedLower") (k2 := "flippedUpper") (a := "_feeGrowthGlobal1X128")
    (.bool false) (.bool false) (by native_decide) (by native_decide)]
  exact store_get_self
    ((burnModifyPositionAfterPositionKeyFrame v σ I).locals.insert
      "_feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
    "_feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I)

theorem burnAfterFeeGrowthInsideFrame_positionKey {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthInsideFrame v σ I).locals.get? "_positionKey" =
      some (burnPositionKeyValue I) := by
  rw [burnModifyPositionAfterFeeGrowthInsideFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    (k := "feeGrowthInside") (a := "_positionKey")
    (.tuple [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I])
    (by native_decide)]
  exact burnAfterFeeGrowthGlobalsFrame_positionKey σ I

theorem burnAfterFeeGrowthInsideFrame_liquidityDelta {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthInsideFrame v σ I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionAfterFeeGrowthInsideFrame]
  rw [store_get_ne (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    (k := "feeGrowthInside") (a := "liquidityDelta")
    (.tuple [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I])
    (by native_decide)]
  exact burnAfterFeeGrowthGlobalsFrame_liquidityDelta σ I

theorem burnAfterFeeGrowthInsideFrame_feeGrowthInside {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthInsideFrame v σ I).locals.get? "feeGrowthInside" =
      some (.tuple [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I]) := by
  rw [burnModifyPositionAfterFeeGrowthInsideFrame]
  exact store_get_self (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals
    "feeGrowthInside"
    (.tuple [burnTickGetInside0Value σ I, burnTickGetInside1Value σ I])

theorem burnModifyPosition_evalTickGetFeeGrowthInsideArgs {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExprs? (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .var "tickLower", .var "tickUpper", .var "_slot0tick",
        .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128" ] =
      .ok (burnTickGetFeeGrowthInsideArgValues σ I) := by
  simp only [burnTickGetFeeGrowthInsideArgValues, evalExprs?, evalExpr?,
    EvalResult.bind, bind, pure]
  rw [burnAfterFeeGrowthGlobalsFrame_tickLower (v := v),
    burnAfterFeeGrowthGlobalsFrame_tickUpper (v := v),
    burnAfterFeeGrowthGlobalsFrame_slot0tick (v := v),
    burnAfterFeeGrowthGlobalsFrame_feeGrowthGlobal0 (v := v),
    burnAfterFeeGrowthGlobalsFrame_feeGrowthGlobal1 (v := v)]
  rfl

theorem burnModifyPosition_evalPositionUpdateArgsAfterFeeGrowthInside
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExprs? (config v) (burnModifyPositionAfterFeeGrowthInsideFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [ .var "_positionKey", .var "liquidityDelta", tuple0 (.var "feeGrowthInside"),
        tuple1 (.var "feeGrowthInside") ] =
      .ok (burnPositionUpdateValueArgValues I
        (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I)) := by
  simp only [burnPositionUpdateValueArgValues, evalExprs?, evalExpr?, tuple0, tuple1,
    EvalResult.bind, bind, pure]
  rw [burnAfterFeeGrowthInsideFrame_positionKey (v := v),
    burnAfterFeeGrowthInsideFrame_liquidityDelta (v := v),
    burnAfterFeeGrowthInsideFrame_feeGrowthInside (v := v)]
  rfl

theorem uniswapV3PoolLookupTickGetFeeGrowthInside (v : PoolImmutables) :
    lookupCallable? (contract v) "tickGetFeeGrowthInside" =
      some tickGetFeeGrowthInsideFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
    getTickAtSqrtRatioFunction, oracleLteFunction, oracleTransformFunction,
    getSurroundingObservationsFunction, observeSingleFunction, observeBodyFunction,
    liquidityAddDeltaFunction, oracleWriteFunction, tickGetFeeGrowthInsideFunction,
    tickUpdateFunction, tickClearFunction, tickBitmapFlipFunction, positionUpdateFunction,
    getAmount0DeltaUnsignedFunction, getAmount1DeltaUnsignedFunction,
    getAmount0DeltaSignedFunction, getAmount1DeltaSignedFunction, modifyPositionFunction]

theorem uniswapV3PoolLookupPositionUpdate (v : PoolImmutables) :
    lookupCallable? (contract v) "positionUpdate" =
      some positionUpdateFunction.toCallable := by
  simp [lookupCallable?, lookupFunction?, contract, functions, getSqrtRatioAtTickFunction,
    getTickAtSqrtRatioFunction, oracleLteFunction, oracleTransformFunction,
    getSurroundingObservationsFunction, observeSingleFunction, observeBodyFunction,
    liquidityAddDeltaFunction, oracleWriteFunction, tickGetFeeGrowthInsideFunction,
    tickUpdateFunction, tickClearFunction, tickBitmapFlipFunction, positionUpdateFunction,
    getAmount0DeltaUnsignedFunction, getAmount1DeltaUnsignedFunction,
    getAmount0DeltaSignedFunction, getAmount1DeltaSignedFunction, modifyPositionFunction]

theorem uniswapV3PoolModifyPositionSourcePositionUpdateLiquidityZeroTailReverts
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (burnModifyPositionAfterLiquidityDeltaTail v)
      .reverted := by
  change ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
    (initState cA gh bl σ σ₀ g A I)
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
    .reverted
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
  · refine ExecBlock.consRevert ?_
    refine internalCallFunctionRevert (callee := positionUpdateFunction)
      (argVals := burnPositionUpdateValueArgValues I
        (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I))
      (locals := burnPositionUpdateValueStore I
        (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I))
      ?_ ?_ ?_ ?_
    · exact burnModifyPosition_evalPositionUpdateArgsAfterFeeGrowthInside
        (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
        (σ₀ := σ₀) (A := A) (I := I) (g := g)
    · simpa [burnModifyPositionAfterFeeGrowthInsideFrame] using
        uniswapV3PoolLookupPositionUpdate v
    · exact burnPositionUpdateValue_bindParams I
        (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I)
    · simpa [burnPositionUpdateValueFrame, burnModifyPositionAfterFeeGrowthInsideFrame] using
        uniswapV3PoolPositionUpdateSourceLiquidityZeroRevertsValue (v := v)
          (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
          (A := A) (I := I) (g := g)
          (burnTickGetInside0Value σ I) (burnTickGetInside1Value σ I) hzero hliq

theorem uniswapV3PoolModifyPositionSourcePositionUpdateLiquidityZeroReverts
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
        (solcSlotWord σ I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
    ExecFuncBody (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I) (modifyPositionFunction v).body .reverted := by
  refine ExecFuncBody.execBlockRevert ?_
  have hprefix := uniswapV3PoolModifyPositionSourceThroughLiquidityDeltaZeroSkip
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hguard htickLt hge hle hzero
  have htail := uniswapV3PoolModifyPositionSourcePositionUpdateLiquidityZeroTailReverts
    (v := v) (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
    (A := A) (I := I) (g := g) hzero hliq
  simpa [modifyPositionFunction, burnModifyPositionSlot0Prefix,
    burnModifyPositionPositionKeyStep, burnModifyPositionFeeGrowthGlobalsStep,
    burnModifyPositionLiquidityDeltaUpdateStep, burnModifyPositionAfterLiquidityDeltaTail]
    using execBlock_append hprefix htail

theorem uniswapV3PoolBurnSourcePositionUpdateLiquidityZeroReverts
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
    (hzero : burnAmountCleanWord I = ⟨0⟩)
    (hliq :
      burnPositionUpdateSlot0Packed
        (solcSlotWord (sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
          I (positionsBase (burnPositionKeyKey I))) = ⟨0⟩) :
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
    · exact uniswapV3PoolModifyPositionSourcePositionUpdateLiquidityZeroReverts
        (v := v) (cA := cA) (gh := gh) (bl := bl)
        (σ := sstoreAccountMap I.codeOwner σ ⟨0⟩ (burnLockedSlotWord σ I))
        (σ₀ := σ₀) (A := A) (I := I) (g := g) hguard htickLt hge hle hzero
        hliq
  simpa [burnTransition, nonpayable, lockPrefix] using
    execBlock_append hprefix (ExecBlock.consRevert hstmt)

end Benchmarks.UniswapV3Pool
