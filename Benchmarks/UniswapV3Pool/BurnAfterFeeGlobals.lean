import Benchmarks.UniswapV3Pool.BurnAfterCheckTicks

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

def burnModifyPositionLiquidityDeltaUpdateStep (v : PoolImmutables) : List Stmt :=
  [ Stmt.ite (neE (.var "liquidityDelta") (.intLit 0))
      [ .letDecl "time" (some uint32) blockTimestamp32,
        .internalCall "observeSingle"
          [ .var "time", .intLit 0, .storage (slot0F "tick"),
            .storage (slot0F "observationIndex"), .storage liquidityRef,
            .storage (slot0F "observationCardinality") ]
          "observedForUpdate",
        .internalCall "tickUpdate"
          [ .var "tickLower", .var "_slot0tick", .var "liquidityDelta",
            .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128",
            tuple1 (.var "observedForUpdate"), tuple0 (.var "observedForUpdate"),
            .var "time", .boolLit false, .intLit v.maxLiquidityPerTick ]
          "flippedLowerCall",
        .assign .localVar (varRef "flippedLower") (.var "flippedLowerCall"),
        .internalCall "tickUpdate"
          [ .var "tickUpper", .var "_slot0tick", .var "liquidityDelta",
            .var "_feeGrowthGlobal0X128", .var "_feeGrowthGlobal1X128",
            tuple1 (.var "observedForUpdate"), tuple0 (.var "observedForUpdate"),
            .var "time", .boolLit true, .intLit v.maxLiquidityPerTick ]
          "flippedUpperCall",
        .assign .localVar (varRef "flippedUpper") (.var "flippedUpperCall"),
        Stmt.ite (.var "flippedLower")
          [ .internalCall "tickBitmapFlip" [.var "tickLower", .intLit v.tickSpacing]
              "_flipLower" ]
          [],
        Stmt.ite (.var "flippedUpper")
          [ .internalCall "tickBitmapFlip" [.var "tickUpper", .intLit v.tickSpacing]
              "_flipUpper" ]
          [] ]
      [] ]

theorem burnModifyPositionStore_liquidityDelta (I : ExecutionEnv) :
    (burnModifyPositionStore I).get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionStore]
  rw [store_get_ne3 ((∅ : Store).insert "liquidityDelta" (burnLiquidityDeltaValue I))
    (k1 := "tickUpper") (k2 := "tickLower") (k3 := "owner")
    (a := "liquidityDelta") (burnTickUpperValue I) (burnTickLowerValue I)
    (.address I.source) (by native_decide) (by native_decide) (by native_decide)]
  exact store_get_self (∅ : Store) "liquidityDelta" (burnLiquidityDeltaValue I)

theorem burnAfterSlot0Frame_liquidityDelta {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterSlot0Frame v σ I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionAfterSlot0Frame]
  rw [store_get_ne5 (burnModifyPositionStore I)
    (k1 := "_slot0sqrtPriceX96") (k2 := "_slot0tick")
    (k3 := "_slot0observationIndex") (k4 := "_slot0observationCardinality")
    (k5 := "_slot0observationCardinalityNext") (a := "liquidityDelta")
    (burnSlot0SqrtPriceX96Value σ I) (burnSlot0TickValue σ I)
    (burnSlot0ObservationIndexValue σ I) (burnSlot0ObservationCardinalityValue σ I)
    (burnSlot0ObservationCardinalityNextValue σ I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)]
  exact burnModifyPositionStore_liquidityDelta I

theorem burnAfterPositionKeyFrame_liquidityDelta {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterPositionKeyFrame v σ I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionAfterPositionKeyFrame]
  rw [store_get_ne (burnModifyPositionAfterSlot0Frame v σ I).locals
    (k := "_positionKey") (a := "liquidityDelta") (burnPositionKeyValue I)
    (by native_decide)]
  exact burnAfterSlot0Frame_liquidityDelta σ I

theorem burnAfterFeeGrowthGlobalsFrame_liquidityDelta {v : PoolImmutables}
    (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I).locals.get? "liquidityDelta" =
      some (burnLiquidityDeltaValue I) := by
  rw [burnModifyPositionAfterFeeGrowthGlobalsFrame]
  rw [store_get_ne4 (burnModifyPositionAfterPositionKeyFrame v σ I).locals
    (k1 := "_feeGrowthGlobal0X128") (k2 := "_feeGrowthGlobal1X128")
    (k3 := "flippedLower") (k4 := "flippedUpper") (a := "liquidityDelta")
    (burnFeeGrowthGlobal0Value σ I) (burnFeeGrowthGlobal1Value σ I)
    (.bool false) (.bool false)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)]
  exact burnAfterPositionKeyFrame_liquidityDelta σ I

theorem burnEvalLiquidityDeltaNeZeroFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    evalExpr? (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool false) := by
  simp only [neE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnAfterFeeGrowthGlobalsFrame_liquidityDelta (v := v) σ I]
  simp [EvalResult.ofOption, evalBinaryOp?, burnLiquidityDeltaValue, hzero]

theorem burnEvalLiquidityDeltaNeZeroTrue {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩) :
    evalExpr? (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (neE (.var "liquidityDelta") (.intLit 0)) = .ok (.bool true) := by
  simp only [neE, evalExpr?, EvalResult.bind, bind, pure]
  rw [burnAfterFeeGrowthGlobalsFrame_liquidityDelta (v := v) σ I]
  simp [EvalResult.ofOption, evalBinaryOp?, burnLiquidityDeltaValue]
  have hnat : (burnAmountCleanWord I).toNat ≠ 0 := by
    intro h
    exact hnonzero (uint256_toNat_eq_zero h)
  omega

theorem uniswapV3PoolModifyPositionSourceLiquidityDeltaZeroSkip {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    ExecBlock (config v) (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (burnModifyPositionLiquidityDeltaUpdateStep v)
      (ExecResult.ok (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  refine ExecBlock.consNormal (ExecStmt.iteFalse ?_ ?_) ExecBlock.nil
  · exact burnEvalLiquidityDeltaNeZeroFalse (v := v) (cA := cA) (gh := gh)
      (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hzero
  · exact ExecBlock.nil

theorem uniswapV3PoolModifyPositionSourceThroughLiquidityDeltaZeroSkip
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I))
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper") ++
        burnModifyPositionSlot0Prefix ++ burnModifyPositionPositionKeyStep ++
        burnModifyPositionFeeGrowthGlobalsStep ++
        burnModifyPositionLiquidityDeltaUpdateStep v)
      (ExecResult.ok (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolModifyPositionSourceThroughFeeGrowthGlobals (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge hle
  exact execBlock_append hprefix
    (uniswapV3PoolModifyPositionSourceLiquidityDeltaZeroSkip (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hzero)

abbrev burnTickLowerFeeGrowthCompareWord (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩
    (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))

abbrev burnTickUpperFeeGrowthCompareWord (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩
    (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))

abbrev burnTickLowerFeeGrowthKey (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (burnTickLowerFeeGrowthCompareWord I)

abbrev burnTickUpperFeeGrowthKey (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (burnTickUpperFeeGrowthCompareWord I)

abbrev burnTickLowerFeeGrowthBaseSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨5⟩ (burnTickLowerFeeGrowthKey I)

abbrev burnTickUpperFeeGrowthBaseSlot (I : ExecutionEnv) : UInt256 :=
  solcMappingSlot ⟨5⟩ (burnTickUpperFeeGrowthKey I)

abbrev burnTickLowerFeeGrowthOutside0Slot (I : ExecutionEnv) : UInt256 :=
  (⟨1⟩ : UInt256) + burnTickLowerFeeGrowthBaseSlot I

abbrev burnTickLowerFeeGrowthOutside1Slot (I : ExecutionEnv) : UInt256 :=
  (⟨2⟩ : UInt256) + burnTickLowerFeeGrowthBaseSlot I

abbrev burnTickLowerFeeGrowthOutside0Word (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (burnTickLowerFeeGrowthOutside0Slot I)

abbrev burnTickLowerFeeGrowthOutside1Word (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (burnTickLowerFeeGrowthOutside1Slot I)

abbrev burnTickUpperFeeGrowthOutside0Slot (I : ExecutionEnv) : UInt256 :=
  (⟨1⟩ : UInt256) + burnTickUpperFeeGrowthBaseSlot I

abbrev burnTickUpperFeeGrowthOutside1Slot (I : ExecutionEnv) : UInt256 :=
  (⟨2⟩ : UInt256) + burnTickUpperFeeGrowthBaseSlot I

abbrev burnTickUpperFeeGrowthOutside0Word (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (burnTickUpperFeeGrowthOutside0Slot I)

abbrev burnTickUpperFeeGrowthOutside1Word (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (burnTickUpperFeeGrowthOutside1Slot I)

noncomputable abbrev burnTickLowerFeeGrowthMem (σ : AccountMap)
    (I : ExecutionEnv) : ByteArray :=
  twoWordHashMem (burnTickLowerFeeGrowthKey I) ⟨5⟩
    (burnPositionKeyMappingMem σ I)

noncomputable abbrev burnTickUpperFeeGrowthMem (σ : AccountMap)
    (I : ExecutionEnv) : ByteArray :=
  wordAt0Mem (burnTickUpperFeeGrowthKey I) (burnTickLowerFeeGrowthMem σ I)

theorem wordAt0Mem_size_of_size_ge {mem : ByteArray} (word : UInt256)
    (hmem : 32 ≤ mem.size) :
    (wordAt0Mem word mem).size = mem.size := by
  unfold wordAt0Mem
  rw [write32_eq _ _ _ (by rw [toByteArray_size]) (by omega),
    ByteArray.size_append, ByteArray.size_append, ByteArray.size_extract,
    ByteArray.size_extract, ByteArray.size_extract, toByteArray_size]
  omega

theorem wordAt0Mem_twoWordHashMem_read0_64_of_size_ge
    {mem : ByteArray} (key newKey slot : UInt256) (hmem : 64 ≤ mem.size) :
    (wordAt0Mem newKey (twoWordHashMem key slot mem)).readWithPadding 0 64 =
      UInt256.toByteArray newKey ++ UInt256.toByteArray slot := by
  have hbaseSize :
      (twoWordHashMem key slot mem).size = mem.size :=
    twoWordHashMem_size_of_size_ge key slot hmem
  have hsize :
      (wordAt0Mem newKey (twoWordHashMem key slot mem)).size = mem.size := by
    rw [wordAt0Mem_size_of_size_ge]
    · exact hbaseSize
    · rw [hbaseSize]
      omega
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
  have hleft :
      (wordAt0Mem newKey (twoWordHashMem key slot mem)).extract 0 32 =
        UInt256.toByteArray newKey := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hsize]; omega),
      wordAt0Mem_read0]
  have hright :
      (wordAt0Mem newKey (twoWordHashMem key slot mem)).extract 32 64 =
        UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hsize]; omega)]
    unfold wordAt0Mem
    rw [write32_read_above _ _ 0 32 (by rw [toByteArray_size])
      (by omega) (by omega) (by rw [hbaseSize]; omega)]
    exact twoWordHashMem_read32_of_size_ge key slot hmem
  rw [show (wordAt0Mem newKey (twoWordHashMem key slot mem)).extract 0 64 =
      (wordAt0Mem newKey (twoWordHashMem key slot mem)).extract 0 32 ++
        (wordAt0Mem newKey (twoWordHashMem key slot mem)).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]

theorem wordAt0Mem_twoWordHashMem_solcMappingSlot_of_size_ge
    (baseSlot key newKey : UInt256) {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((wordAt0Mem newKey (twoWordHashMem key baseSlot mem)).readWithPadding
          0 64))) =
      solcMappingSlot baseSlot newKey := by
  rw [wordAt0Mem_twoWordHashMem_read0_64_of_size_ge key newKey baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single newKey baseSlot

theorem burnPositionKeyMappingMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMappingMem σ I).size = 567 := by
  unfold burnPositionKeyMappingMem
  rw [twoWordHashMem_size_of_size_ge]
  · exact burnPositionKeyPackedHashMem_size σ I
  · rw [burnPositionKeyPackedHashMem_size σ I]
    omega

theorem burnTickLowerFeeGrowthMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickLowerFeeGrowthMem σ I).size = 567 := by
  unfold burnTickLowerFeeGrowthMem
  rw [twoWordHashMem_size_of_size_ge]
  · exact burnPositionKeyMappingMem_size σ I
  · rw [burnPositionKeyMappingMem_size σ I]
    omega

theorem burnTickUpperFeeGrowthMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnTickUpperFeeGrowthMem σ I).size = 567 := by
  unfold burnTickUpperFeeGrowthMem
  rw [wordAt0Mem_size_of_size_ge]
  · exact burnTickLowerFeeGrowthMem_size σ I
  · rw [burnTickLowerFeeGrowthMem_size σ I]
    omega

theorem burnFeeGrowthInsideLowerSlt_eq (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I))
        (burnTickLowerFeeGrowthCompareWord I) =
      if tickSpacingSint24Value (slot0TickRawWord σ I) <
          tickSpacingSint24Value (burnTickLowerWord I) then ⟨1⟩ else ⟨0⟩ := by
  simp only [slot0TickReturnWord, burnTickLowerFeeGrowthCompareWord,
    burnTickLowerCleanWord]
  rw [signextend_two_tickSpacing_idempotent
    (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 20))]
  rw [signextend_two_tickSpacing_idempotent
    (UInt256.signextend ⟨2⟩ (burnTickLowerWord I))]
  rw [signextend_two_tickSpacing_idempotent (burnTickLowerWord I)]
  rw [← slot0TickRawValue_wordOfInt
    (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 20))]
  rw [← wordOfInt_sint24Value_eq_signextend_two (burnTickLowerWord I)]
  exact slt_wordOfInt_int24 _ _ (tickSpacingSint24Value_ge _)
    (tickSpacingSint24Value_lt _) (tickSpacingSint24Value_ge _)
    (tickSpacingSint24Value_lt _)

theorem burnFeeGrowthInsideLowerSlt_ne_zero (σ : AccountMap) (I : ExecutionEnv)
    (hlt :
      tickSpacingSint24Value (slot0TickRawWord σ I) <
        tickSpacingSint24Value (burnTickLowerWord I)) :
    UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I))
        (burnTickLowerFeeGrowthCompareWord I) ≠ ⟨0⟩ := by
  rw [burnFeeGrowthInsideLowerSlt_eq σ I, if_pos hlt]
  native_decide

theorem burnFeeGrowthInsideLowerSlt_eq_zero (σ : AccountMap) (I : ExecutionEnv)
    (hge :
      ¬ tickSpacingSint24Value (slot0TickRawWord σ I) <
        tickSpacingSint24Value (burnTickLowerWord I)) :
    UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I))
        (burnTickLowerFeeGrowthCompareWord I) = ⟨0⟩ := by
  rw [burnFeeGrowthInsideLowerSlt_eq σ I, if_neg hge]

theorem burnFeeGrowthInsideUpperSlt_eq (σ : AccountMap) (I : ExecutionEnv) :
    UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I))
        (burnTickUpperFeeGrowthCompareWord I) =
      if tickSpacingSint24Value (slot0TickRawWord σ I) <
          tickSpacingSint24Value (burnTickUpperWord I) then ⟨1⟩ else ⟨0⟩ := by
  simp only [slot0TickReturnWord, burnTickUpperFeeGrowthCompareWord,
    burnTickUpperCleanWord]
  rw [signextend_two_tickSpacing_idempotent
    (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 20))]
  rw [signextend_two_tickSpacing_idempotent
    (UInt256.signextend ⟨2⟩ (burnTickUpperWord I))]
  rw [signextend_two_tickSpacing_idempotent (burnTickUpperWord I)]
  rw [← slot0TickRawValue_wordOfInt
    (UInt256.div (slot0SlotWord σ I) (slot0ShiftBytes 20))]
  rw [← wordOfInt_sint24Value_eq_signextend_two (burnTickUpperWord I)]
  exact slt_wordOfInt_int24 _ _ (tickSpacingSint24Value_ge _)
    (tickSpacingSint24Value_lt _) (tickSpacingSint24Value_ge _)
    (tickSpacingSint24Value_lt _)

theorem burnFeeGrowthInsideUpperSlt_ne_zero (σ : AccountMap) (I : ExecutionEnv)
    (hlt :
      tickSpacingSint24Value (slot0TickRawWord σ I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I))
        (burnTickUpperFeeGrowthCompareWord I) ≠ ⟨0⟩ := by
  rw [burnFeeGrowthInsideUpperSlt_eq σ I, if_pos hlt]
  native_decide

theorem burnFeeGrowthInsideUpperSlt_eq_zero (σ : AccountMap) (I : ExecutionEnv)
    (hge :
      ¬ tickSpacingSint24Value (slot0TickRawWord σ I) <
        tickSpacingSint24Value (burnTickUpperWord I)) :
    UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ I))
        (burnTickUpperFeeGrowthCompareWord I) = ⟨0⟩ := by
  rw [burnFeeGrowthInsideUpperSlt_eq σ I, if_neg hge]

private theorem uniswapV3PoolBurnAfterFeeGlobalsDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 16264 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
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
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolPatchPreservesJumpDest19492 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨19492⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched19492 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨19492⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest19492

private theorem uniswapV3PoolPatchPreservesJumpDest19510 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨19510⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched19510 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨19510⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest19510

theorem burnLiquidityDeltaZeroJumpCond (I : ExecutionEnv)
    (hzero : burnAmountCleanWord I = ⟨0⟩) :
    UInt256.isZero
      (UInt256.signextend ⟨15⟩
        (UInt256.signextend ⟨15⟩
          (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))) ≠ ⟨0⟩ := by
  rw [hzero]
  native_decide

theorem signextend_fifteen_zero_sub_ne_zero_of_lt {w : UInt256}
    (hnonzero : w ≠ ⟨0⟩) (hlt : w.toNat < EVM.twoPow 127) :
    UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ w) ≠ ⟨0⟩ := by
  have htoNatNe : w.toNat ≠ 0 := by
    intro h
    exact hnonzero (uint256_toNat_eq_zero h)
  have hpos : 0 < w.toNat := Nat.pos_of_ne_zero htoNatNe
  have hsubNat : (UInt256.sub (⟨0⟩ : UInt256) w).toNat = UInt256.size - w.toNat := by
    have hsub := usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w) hpos
    simpa using hsub
  have hposInt : (0 : Int) < (w.toNat : Int) := by exact_mod_cast hpos
  have hneg : -(Int.ofNat w.toNat) < 0 := by
    have : (0 : Int) < Int.ofNat w.toNat := by simpa using hposInt
    omega
  have habs : (-(Int.ofNat w.toNat)).natAbs = w.toNat := by
    rw [Int.natAbs_neg]
    simp
  have hword : UInt256.sub (⟨0⟩ : UInt256) w =
      EVM.wordOfInt (-(Int.ofNat w.toNat)) := by
    apply u256_inj
    rw [hsubNat]
    have hltWord : (-(Int.ofNat w.toNat)).natAbs < EVM.wordModulus := by
      rw [habs]
      rw [show EVM.wordModulus = UInt256.size by native_decide]
      exact w.val.isLt
    rw [wordOfInt_neg_toNat_lt_wordModulus _ hneg hltWord]
    rw [habs]
  rw [hword]
  rw [signextend_fifteen_wordOfInt_ticks]
  · intro hwzero
    have hto := congrArg UInt256.toNat hwzero
    have hltWord : (-(Int.ofNat w.toNat)).natAbs < EVM.wordModulus := by
      rw [habs]
      rw [show EVM.wordModulus = UInt256.size by native_decide]
      exact w.val.isLt
    rw [wordOfInt_neg_toNat_lt_wordModulus _ hneg hltWord] at hto
    rw [habs] at hto
    change UInt256.size - w.toNat = 0 at hto
    have hwlt : w.toNat < UInt256.size := w.val.isLt
    omega
  · norm_num [EVM.twoPow] at hlt ⊢
    omega
  · norm_num [EVM.twoPow] at hlt ⊢
    omega

theorem signextend_fifteen_zero_sub_slt_zero_of_lt {w : UInt256}
    (hnonzero : w ≠ ⟨0⟩) (hlt : w.toNat < EVM.twoPow 127) :
    UInt256.slt (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ w)) ⟨0⟩ = ⟨1⟩ := by
  have htoNatNe : w.toNat ≠ 0 := by
    intro h
    exact hnonzero (uint256_toNat_eq_zero h)
  have hpos : 0 < w.toNat := Nat.pos_of_ne_zero htoNatNe
  have hsubNat : (UInt256.sub (⟨0⟩ : UInt256) w).toNat = UInt256.size - w.toNat := by
    simpa using usub_toNat_underflow (a := (⟨0⟩ : UInt256)) (b := w) hpos
  have hposInt : (0 : Int) < (w.toNat : Int) := by exact_mod_cast hpos
  have hneg : -(Int.ofNat w.toNat) < 0 := by
    have : (0 : Int) < Int.ofNat w.toNat := by simpa using hposInt
    omega
  have habs : (-(Int.ofNat w.toNat)).natAbs = w.toNat := by
    rw [Int.natAbs_neg]
    simp
  have hword : UInt256.sub (⟨0⟩ : UInt256) w =
      EVM.wordOfInt (-(Int.ofNat w.toNat)) := by
    apply u256_inj
    rw [hsubNat]
    have hltWord : (-(Int.ofNat w.toNat)).natAbs < EVM.wordModulus := by
      rw [habs, show EVM.wordModulus = UInt256.size by native_decide]
      exact w.val.isLt
    rw [wordOfInt_neg_toNat_lt_wordModulus _ hneg hltWord, habs]
  rw [hword, signextend_fifteen_wordOfInt_ticks]
  · apply slt_lit_one_high (m := 0)
    · norm_num
    · have hltWord : (-(Int.ofNat w.toNat)).natAbs < EVM.wordModulus := by
        rw [habs, show EVM.wordModulus = UInt256.size by native_decide]
        exact w.val.isLt
      rw [wordOfInt_neg_toNat_lt_wordModulus _ hneg hltWord, habs]
      norm_num [UInt256.size, EVM.twoPow] at hlt ⊢
      omega
  · norm_num [EVM.twoPow] at hlt ⊢
    omega
  · norm_num [EVM.twoPow] at hlt ⊢
    omega

theorem burnLiquidityDeltaNonzeroJumpCond (I : ExecutionEnv)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩) :
    UInt256.isZero
      (UInt256.signextend ⟨15⟩
        (UInt256.signextend ⟨15⟩
          (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))) = ⟨0⟩ := by
  rw [ticksSignextendFifteen_idempotent]
  apply isZero_eq_zero_of_ne
  exact signextend_fifteen_zero_sub_ne_zero_of_lt hnonzero
    (signextend_fifteen_eq_self_toNat_lt_twoPow127
      (by simpa [burnAmountCleanWord] using uint128Mask_bound (burnAmountWord I))
      hcanon)

theorem burnLiquidityDeltaNegativeSltJumpCond (I : ExecutionEnv)
    (hcanon :
      UInt256.signextend ⟨15⟩ (burnAmountCleanWord I) = burnAmountCleanWord I)
    (hnonzero : burnAmountCleanWord I ≠ ⟨0⟩) :
    UInt256.isZero
      (UInt256.slt
        (UInt256.signextend ⟨15⟩
          (UInt256.signextend ⟨15⟩
            (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))))
        ⟨0⟩) = ⟨0⟩ := by
  rw [ticksSignextendFifteen_idempotent]
  rw [signextend_fifteen_zero_sub_slt_zero_of_lt hnonzero
    (signextend_fifteen_eq_self_toNat_lt_twoPow127
      (by simpa [burnAmountCleanWord] using uint128Mask_bound (burnAmountWord I))
      hcanon)]
  native_decide

theorem uniswapV3PoolBurnAfterFeeGlobalsLiquidityDeltaZeroJump {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcond :
      UInt256.isZero
        (UInt256.signextend ⟨15⟩
          (UInt256.signextend ⟨15⟩
            (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))) ≠ ⟨0⟩)
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
    (hov : R.length + 55 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨19492⟩
      (⟨0⟩ :: ⟨0⟩ ::
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
  have hdec : decode code (⟨19189⟩ : UInt256) =
      decode uniswapV3PoolBytecode (⟨19189⟩ : UInt256) := by
    exact uniswapV3PoolBurnAfterFeeGlobalsDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)
  exact ⟨_, _, h.jumpiT
    (by rw [hdec]; native_decide)
    hcond
    (uniswapV3PoolJumpDestPatched19492 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnAfterFeeGlobalsLiquidityDeltaNonzeroFallthrough
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
    (hov : R.length + 55 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨19190⟩
      (⟨0⟩ :: ⟨0⟩ ::
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
  have hdec : decode code (⟨19189⟩ : UInt256) =
      decode uniswapV3PoolBytecode (⟨19189⟩ : UInt256) := by
    exact uniswapV3PoolBurnAfterFeeGlobalsDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)
  exact ⟨_, _, h.jumpiNT
    (by rw [hdec]; native_decide)
    hcond
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

private theorem uniswapV3PoolBurnAfterFeeGlobalsCallDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 19492 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19559) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 19559 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

private theorem uniswapV3PoolPatchPreservesJumpDest21387 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21387⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21387 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21387⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21387

private theorem uniswapV3PoolPatchPreservesJumpDest21457 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21457⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21457 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21457⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21457

private theorem uniswapV3PoolPatchPreservesJumpDest21476 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21476⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21476 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21476⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21476

private theorem uniswapV3PoolPatchPreservesJumpDest21510 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21510⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21510 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21510⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21510

private theorem uniswapV3PoolPatchPreservesJumpDest21529 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21529⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21529 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21529⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21529

private theorem uniswapV3PoolPatchPreservesJumpDest21559 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨21559⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched21559 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨21559⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest21559

private theorem uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 21387 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21591) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 21591 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (by
      intro p hp
      simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord,
        List.lookup] at hp
      rcases hp with
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals omega)

theorem uniswapV3PoolBurnAfterFeeGlobalsEnterFeeGrowthInside {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨19492⟩
      (⟨0⟩ :: ⟨0⟩ ::
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
    (hov : R.length + 57 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21387⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
  have hdec (pc : UInt256)
      (hlo : 19492 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19559) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnAfterFeeGlobalsCallDecodeEqTemplate hpatch hlo hhi
  have rd19503 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨19510⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨5⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup13 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup13 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd19504 := RD.dup12 rd19503
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd19509 := evm_run rd19504 with [
    raw dup11 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨21387⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd19509.jump
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched21387 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

set_option maxHeartbeats 3000000 in
theorem uniswapV3PoolBurnFeeGrowthInsideLowerBranchTest {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21387⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21440⟩
      (⟨21457⟩ ::
        UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
          (burnTickLowerFeeGrowthCompareWord ee) ::
        ⟨0⟩ :: ⟨0⟩ ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21387 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21591) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch hlo hhi
  have rd21392 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21393 := RD.signextend rd21392
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21395 := evm_run rd21393 with [
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21396 := RD.signextend rd21395
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21400 := evm_run rd21396 with [
    raw push1 ⟨0⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21401 := rd21400.mstore 0
    (wordAt0Mem (burnTickLowerFeeGrowthKey ee) (burnPositionKeyMappingMem σ ee))
    (UInt256.ofNat 18)
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    mem_cost
    (by rfl)
    (by native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21405 := evm_run rd21401 with [
    raw push1 ⟨32⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup10 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21406 := rd21405.mstore 0
    (burnTickLowerFeeGrowthMem σ ee)
    (UInt256.ofNat 18)
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    mem_cost
    (by rfl)
    (by native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21410 := evm_run rd21406 with [
    raw push1 ⟨64⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have hLowerSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnTickLowerFeeGrowthMem σ ee).readWithPadding 0 64))) =
        burnTickLowerFeeGrowthBaseSlot ee := by
    exact twoWordHashMem_solcMappingSlot_of_size_ge ⟨5⟩
      (burnTickLowerFeeGrowthKey ee)
      (by rw [burnPositionKeyMappingMem_size σ ee]; omega)
  have rd21411 := rd21410.keccak256 0 (burnTickLowerFeeGrowthBaseSlot ee)
    (UInt256.ofNat 18)
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hLowerSlot)
    (by native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21413 := evm_run rd21411 with [
    raw dup9 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21414 := RD.signextend rd21413
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21415 := evm_run rd21414 with [
    raw dup6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21416 := RD.signextend rd21415
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21417 := evm_run rd21416 with [
    raw dup4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21418 := rd21417.mstore 0
    (wordAt0Mem (burnTickUpperFeeGrowthKey ee) (burnTickLowerFeeGrowthMem σ ee))
    (UInt256.ofNat 18)
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    mem_cost
    (by rfl)
    (by native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21420 := evm_run rd21418 with [
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have hUpperSlot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnTickUpperFeeGrowthMem σ ee).readWithPadding 0 64))) =
        burnTickUpperFeeGrowthBaseSlot ee := by
    simpa [burnTickUpperFeeGrowthMem, burnTickLowerFeeGrowthMem,
      burnTickUpperFeeGrowthBaseSlot] using
      wordAt0Mem_twoWordHashMem_solcMappingSlot_of_size_ge ⟨5⟩
        (burnTickLowerFeeGrowthKey ee) (burnTickUpperFeeGrowthKey ee)
        (by rw [burnPositionKeyMappingMem_size σ ee]; omega)
  have rd21421 := rd21420.keccak256 0 (burnTickUpperFeeGrowthBaseSlot ee)
    (UInt256.ofNat 18)
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hUpperSlot)
    (by native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21435 := evm_run rd21421 with [
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21436 := RD.signextend rd21435
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21440 := evm_run rd21436 with [
    raw slt (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨21457⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd21440⟩

theorem uniswapV3PoolBurnFeeGrowthInsideLowerBelowJump {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcond :
      UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
          (burnTickLowerFeeGrowthCompareWord ee) ≠ ⟨0⟩)
    (h : RD code ee g s0 ⟨21440⟩
      (⟨21457⟩ ::
        UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
          (burnTickLowerFeeGrowthCompareWord ee) ::
        ⟨0⟩ :: ⟨0⟩ ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21457⟩
      (⟨0⟩ :: ⟨0⟩ ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec : decode code (⟨21440⟩ : UInt256) =
      decode uniswapV3PoolBytecode (⟨21440⟩ : UInt256) := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)
  exact ⟨_, _, h.jumpiT
    (by rw [hdec]; native_decide)
    hcond
    (uniswapV3PoolJumpDestPatched21457 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnFeeGrowthInsideLowerNotBelowFallthrough {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hzero :
      UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
          (burnTickLowerFeeGrowthCompareWord ee) = ⟨0⟩)
    (h : RD code ee g s0 ⟨21440⟩
      (⟨21457⟩ ::
        UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
          (burnTickLowerFeeGrowthCompareWord ee) ::
        ⟨0⟩ :: ⟨0⟩ ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21441⟩
      (⟨0⟩ :: ⟨0⟩ ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec : decode code (⟨21440⟩ : UInt256) =
      decode uniswapV3PoolBytecode (⟨21440⟩ : UInt256) := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)
  exact ⟨_, _, h.jumpiNT
    (by rw [hdec]; native_decide)
    hzero
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnFeeGrowthInsideLowerBelowToJoin {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21457⟩
      (⟨0⟩ :: ⟨0⟩ ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21476⟩
      (UInt256.sub (solcSlotWord σ ee ⟨2⟩)
          (burnTickLowerFeeGrowthOutside1Word σ ee) ::
        UInt256.sub (solcSlotWord σ ee ⟨1⟩)
          (burnTickLowerFeeGrowthOutside0Word σ ee) ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21387 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21591) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch hlo hhi
  have rd21462 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21463⟩ := rd21462.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21467 := evm_run rd21463 with [
    raw dup9 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21471 := evm_run rd21467 with [
    raw dup4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21472⟩ := rd21471.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21476 := evm_run rd21472 with [
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd21476⟩

theorem uniswapV3PoolBurnFeeGrowthInsideLowerNotBelowToJoin {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21441⟩
      (⟨0⟩ :: ⟨0⟩ ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 80 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21476⟩
      (solcSlotWord σ ee (burnTickLowerFeeGrowthBaseSlot ee + ⟨2⟩) ::
        solcSlotWord σ ee (burnTickLowerFeeGrowthBaseSlot ee + ⟨1⟩) ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21387 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21591) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch hlo hhi
  have rd21447 := evm_run h with [
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21448⟩ := rd21447.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21452 := evm_run rd21448 with [
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21453⟩ := rd21452.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21456 := evm_run rd21453 with [
    raw push2 ⟨21476⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd21456.jump
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched21476 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnFeeGrowthInsideUpperBranchTest {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret below1 below0 : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21476⟩
      (below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21493⟩
      (⟨21510⟩ ::
        UInt256.isZero
          (UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
            (burnTickUpperFeeGrowthCompareWord ee)) ::
        ⟨0⟩ :: ⟨0⟩ :: below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21387 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21591) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch hlo hhi
  have rd21480 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21481 := RD.dup12 rd21480
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21483 := evm_run rd21481 with [
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21484 := RD.signextend rd21483
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21485 := RD.dup12 rd21484
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21487 := evm_run rd21485 with [
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21488 := RD.signextend rd21487
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21493 := evm_run rd21488 with [
    raw slt (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw iszero (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨21510⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd21493⟩

theorem uniswapV3PoolBurnFeeGrowthInsideUpperNotInsideJump {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret below1 below0 : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcond :
      UInt256.isZero
        (UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
          (burnTickUpperFeeGrowthCompareWord ee)) ≠ ⟨0⟩)
    (h : RD code ee g s0 ⟨21493⟩
      (⟨21510⟩ ::
        UInt256.isZero
          (UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
            (burnTickUpperFeeGrowthCompareWord ee)) ::
        ⟨0⟩ :: ⟨0⟩ :: below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21510⟩
      (⟨0⟩ :: ⟨0⟩ :: below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec : decode code (⟨21493⟩ : UInt256) =
      decode uniswapV3PoolBytecode (⟨21493⟩ : UInt256) := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)
  exact ⟨_, _, h.jumpiT
    (by rw [hdec]; native_decide)
    hcond
    (uniswapV3PoolJumpDestPatched21510 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnFeeGrowthInsideUpperInsideFallthrough {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret below1 below0 : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hzero :
      UInt256.isZero
        (UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
          (burnTickUpperFeeGrowthCompareWord ee)) = ⟨0⟩)
    (h : RD code ee g s0 ⟨21493⟩
      (⟨21510⟩ ::
        UInt256.isZero
          (UInt256.slt (UInt256.signextend ⟨2⟩ (slot0TickReturnWord σ ee))
            (burnTickUpperFeeGrowthCompareWord ee)) ::
        ⟨0⟩ :: ⟨0⟩ :: below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21494⟩
      (⟨0⟩ :: ⟨0⟩ :: below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec : decode code (⟨21493⟩ : UInt256) =
      decode uniswapV3PoolBytecode (⟨21493⟩ : UInt256) := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch
      (by native_decide) (by native_decide)
  exact ⟨_, _, h.jumpiNT
    (by rw [hdec]; native_decide)
    hzero
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnFeeGrowthInsideUpperInsideToJoin {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret below1 below0 : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21494⟩
      (⟨0⟩ :: ⟨0⟩ :: below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21529⟩
      (solcSlotWord σ ee (burnTickUpperFeeGrowthBaseSlot ee + ⟨2⟩) ::
        solcSlotWord σ ee (burnTickUpperFeeGrowthBaseSlot ee + ⟨1⟩) ::
        below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21387 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21591) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch hlo hhi
  have rd21500 := evm_run h with [
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21501⟩ := rd21500.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21505 := evm_run rd21501 with [
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21506⟩ := rd21505.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21509 := evm_run rd21506 with [
    raw push2 ⟨21529⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd21509.jump
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched21529 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnFeeGrowthInsideUpperNotInsideToJoin {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret below1 below0 : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨21510⟩
      (⟨0⟩ :: ⟨0⟩ :: below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (hov : R.length + 82 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21529⟩
      (UInt256.sub (solcSlotWord σ ee ⟨2⟩)
          (burnTickUpperFeeGrowthOutside1Word σ ee) ::
        UInt256.sub (solcSlotWord σ ee ⟨1⟩)
          (burnTickUpperFeeGrowthOutside0Word σ ee) ::
        below1 :: below0 ::
        burnTickUpperFeeGrowthBaseSlot ee :: burnTickLowerFeeGrowthBaseSlot ee ::
        ⟨0⟩ :: ⟨0⟩ ::
        solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
      (burnTickUpperFeeGrowthMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21387 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21591) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch hlo hhi
  have rd21515 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21516⟩ := rd21515.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21520 := evm_run rd21516 with [
    raw dup11 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21524 := evm_run rd21520 with [
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd21525⟩ := rd21524.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21529 := evm_run rd21525 with [
    raw dup10 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd21529⟩

theorem uniswapV3PoolBurnFeeGrowthInsideJoinReturn {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret above1 above0 below1 below0 upperBase lowerBase z0 z1 fee1 fee0 tick upper lower marker :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hdest : (D_J code 0).contains ret = true)
    (h : RD code ee g s0 ⟨21529⟩
      (above1 :: above0 :: below1 :: below0 :: upperBase :: lowerBase :: z0 :: z1 ::
        fee1 :: fee0 :: tick :: upper :: lower :: marker :: ret :: R)
      mem aw rdata acc k C)
    (hov : R.length + 15 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (UInt256.sub (UInt256.sub fee1 below1) above1 ::
        UInt256.sub (UInt256.sub fee0 below0) above0 :: R)
      mem aw rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 21387 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 21591) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnFeeGrowthInsideSetupDecodeEqTemplate hpatch hlo hhi
  have rd21532 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21533 := RD.swap9 rd21532
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21538 := evm_run rd21533 with [
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21539 := RD.swap12 rd21538
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by omega)
  have rd21547 := evm_run rd21539 with [
    raw swap7 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd21548 := RD.swap9 rd21547
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd21558 := evm_run rd21548 with [
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap7 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd21558.jump
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    hdest
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnFeeGrowthInsideEnterPositionUpdate {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {inside1 inside0 z0 z1 z2 z3 fee1 fee0 posBase tick delta upper lower owner ret free :
      UInt256}
    {R : List UInt256} {mem : ByteArray} {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨19510⟩
      (inside1 :: inside0 :: z0 :: z1 :: z2 :: z3 :: fee1 :: fee0 :: posBase ::
        tick :: delta :: upper :: lower :: owner :: ret :: free :: R)
      mem aw rdata acc k C)
    (hov : R.length + 20 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21559⟩
      (inside1 :: inside0 :: delta :: posBase :: ⟨19527⟩ :: inside1 :: inside0 ::
        z2 :: z3 :: fee1 :: fee0 :: posBase :: tick :: delta :: upper :: lower ::
        owner :: ret :: free :: R)
      mem aw rdata acc k' C' := by
  have hdec (pc : UInt256)
      (hlo : 19492 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19559) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnAfterFeeGlobalsCallDecodeEqTemplate hpatch hlo hhi
  have rd19526 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨19527⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup11 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨21559⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, rd19526.jump
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched21559 hpatch)
    (by simp only [List.length_cons] at hov ⊢; omega)⟩

theorem uniswapV3PoolBurnAfterFeeGlobalsZeroToFeeGrowthInside {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hzero : burnAmountCleanWord ee = ⟨0⟩)
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
    (hov : R.length + 57 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨21387⟩
      (solcSlotWord σ ee ⟨2⟩ :: solcSlotWord σ ee ⟨1⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        ⟨5⟩ :: ⟨19510⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
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
  obtain ⟨_, _, hrdZero⟩ :=
    uniswapV3PoolBurnAfterFeeGlobalsLiquidityDeltaZeroJump (v := v) (code := code)
      (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
      (cA := cA) (σ := σ) hpatch (burnLiquidityDeltaZeroJumpCond ee hzero) h
      (by omega)
  exact uniswapV3PoolBurnAfterFeeGlobalsEnterFeeGrowthInside (v := v) (code := code)
    (ee := ee) (g := g) (s0 := s0) (ret := ret) (R := R) (rdata := rdata)
    (cA := cA) (σ := σ) hpatch hrdZero hov

end Benchmarks.UniswapV3Pool
