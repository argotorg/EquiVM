import Benchmarks.UniswapV3Pool.BurnCheckTicks
import Benchmarks.UniswapV3Pool.InitializeGetTickLogCombine

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

abbrev burnSlot0SqrtPriceX96Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (slot0SqrtPriceX96Word σ I).toNat)

abbrev burnSlot0TickValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  wordToElem (.int int24Int) (slot0TickRawWord σ I)

abbrev burnSlot0ObservationIndexValue (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (slot0ObservationIndexWord σ I).toNat)

abbrev burnSlot0ObservationCardinalityValue (σ : AccountMap) (I : ExecutionEnv) :
    Value :=
  .int (Int.ofNat (slot0ObservationCardinalityWord σ I).toNat)

abbrev burnSlot0ObservationCardinalityNextValue (σ : AccountMap) (I : ExecutionEnv) :
    Value :=
  .int (Int.ofNat (slot0ObservationCardinalityNextWord σ I).toNat)

abbrev burnModifyPositionAfterSlot0Frame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (((((burnModifyPositionStore I)
      |>.insert "_slot0sqrtPriceX96" (burnSlot0SqrtPriceX96Value σ I))
      |>.insert "_slot0tick" (burnSlot0TickValue σ I))
      |>.insert "_slot0observationIndex" (burnSlot0ObservationIndexValue σ I))
      |>.insert "_slot0observationCardinality"
        (burnSlot0ObservationCardinalityValue σ I))
      |>.insert "_slot0observationCardinalityNext"
        (burnSlot0ObservationCardinalityNextValue σ I) }

abbrev burnPositionKeyPackedList (I : ExecutionEnv) : List UInt8 :=
  ((EVM.word I.source).toBytesBE.drop 12) ++
    ((EVM.wordOfInt (tickSpacingSint24Value (burnTickLowerWord I))).toBytesBE.drop 29) ++
    ((EVM.wordOfInt (tickSpacingSint24Value (burnTickUpperWord I))).toBytesBE.drop 29)

abbrev burnPositionKeyPackedBytes (I : ExecutionEnv) : ByteArray :=
  ByteArray.mk (burnPositionKeyPackedList I).toArray

abbrev burnPositionKeyValue (I : ExecutionEnv) : Value :=
  .fixedBytes ⟨31, by decide⟩ (ffi.KEC (burnPositionKeyPackedBytes I)).toList

abbrev burnModifyPositionAfterPositionKeyFrame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnModifyPositionAfterSlot0Frame v σ I).locals.insert "_positionKey"
      (burnPositionKeyValue I) }

abbrev burnFeeGrowthGlobal0Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (solcSlotWord σ I ⟨1⟩).toNat)

abbrev burnFeeGrowthGlobal1Value (σ : AccountMap) (I : ExecutionEnv) : Value :=
  .int (Int.ofNat (solcSlotWord σ I ⟨2⟩).toNat)

abbrev burnModifyPositionAfterFeeGrowthGlobalsFrame
    (v : PoolImmutables) (σ : AccountMap) (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := ((((burnModifyPositionAfterPositionKeyFrame v σ I).locals
      |>.insert "_feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I))
      |>.insert "_feeGrowthGlobal1X128" (burnFeeGrowthGlobal1Value σ I))
      |>.insert "flippedLower" (.bool false))
      |>.insert "flippedUpper" (.bool false) }

def burnModifyPositionSlot0Prefix : List Stmt :=
  [ .letDecl "_slot0sqrtPriceX96" (some uint160) (.storage (slot0F "sqrtPriceX96")),
    .letDecl "_slot0tick" (some int24) (.storage (slot0F "tick")),
    .letDecl "_slot0observationIndex" (some uint16)
      (.storage (slot0F "observationIndex")),
    .letDecl "_slot0observationCardinality" (some uint16)
      (.storage (slot0F "observationCardinality")),
    .letDecl "_slot0observationCardinalityNext" (some uint16)
      (.storage (slot0F "observationCardinalityNext")) ]

def burnModifyPositionPositionKeyStep : List Stmt :=
  [ .letDecl "_positionKey" (some bytes32)
      (positionKey (.var "owner") (.var "tickLower") (.var "tickUpper")) ]

def burnModifyPositionFeeGrowthGlobalsStep : List Stmt :=
  [ .letDecl "_feeGrowthGlobal0X128" (some uint256) (.storage feeGrowthGlobal0X128Ref),
    .letDecl "_feeGrowthGlobal1X128" (some uint256) (.storage feeGrowthGlobal1X128Ref),
    .letDecl "flippedLower" (some boolTy) (.boolLit false),
    .letDecl "flippedUpper" (some boolTy) (.boolLit false) ]

theorem burnEvalSlot0SqrtPriceX96 {v : PoolImmutables}
    {L : Store} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbase : L.get? "slot0" = none) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "sqrtPriceX96")) =
      .ok (burnSlot0SqrtPriceX96Value σ I) := by
  rw [evalExpr_storage_scalar
    (t := .int uint160Int)
    (slot := slot0F "sqrtPriceX96")
    (er := { base := "slot0", steps := [.field "sqrtPriceX96"] })
    (loc := loc ⟨0⟩ ⟨0, by decide⟩ ⟨20, by decide⟩ (by decide)
      (.int uint160Int))
    (hbase := by simpa [slot0F] using hbase)
    (her := by simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
        uint160St])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
  simpa [burnSlot0SqrtPriceX96Value, initState, slot0SqrtPriceX96Word, slot0SlotWord,
    solcSlotWord] using
    slot0StorageLocLoad_sqrtPriceX96 (initState cA gh bl σ σ₀ g A I)

theorem burnEvalSlot0Tick {v : PoolImmutables}
    {L : Store} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbase : L.get? "slot0" = none) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "tick")) =
      .ok (burnSlot0TickValue σ I) := by
  rw [evalExpr_storage_scalar
    (t := .int int24Int)
    (slot := slot0F "tick")
    (er := { base := "slot0", steps := [.field "tick"] })
    (loc := loc ⟨0⟩ ⟨20, by decide⟩ ⟨3, by decide⟩ (by decide)
      (.int int24Int))
    (hbase := by simpa [slot0F] using hbase)
    (her := by simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy, int24St])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
  simpa [burnSlot0TickValue, initState, slot0TickRawWord, slot0SlotWord, solcSlotWord] using
    slot0StorageLocLoad_tick (initState cA gh bl σ σ₀ g A I)

theorem burnEvalSlot0ObservationIndex {v : PoolImmutables}
    {L : Store} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbase : L.get? "slot0" = none) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "observationIndex")) =
      .ok (burnSlot0ObservationIndexValue σ I) := by
  rw [evalExpr_storage_scalar
    (t := .int uint16Int)
    (slot := slot0F "observationIndex")
    (er := { base := "slot0", steps := [.field "observationIndex"] })
    (loc := loc ⟨0⟩ ⟨23, by decide⟩ ⟨2, by decide⟩ (by decide)
      (.int uint16Int))
    (hbase := by simpa [slot0F] using hbase)
    (her := by simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
        uint16St])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
  simpa [burnSlot0ObservationIndexValue, initState, slot0ObservationIndexWord,
    slot0SlotWord, solcSlotWord] using
    slot0StorageLocLoad_observationIndex (initState cA gh bl σ σ₀ g A I)

theorem burnEvalSlot0ObservationCardinality {v : PoolImmutables}
    {L : Store} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbase : L.get? "slot0" = none) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I) (.storage (slot0F "observationCardinality")) =
      .ok (burnSlot0ObservationCardinalityValue σ I) := by
  rw [evalExpr_storage_scalar
    (t := .int uint16Int)
    (slot := slot0F "observationCardinality")
    (er := { base := "slot0", steps := [.field "observationCardinality"] })
    (loc := loc ⟨0⟩ ⟨25, by decide⟩ ⟨2, by decide⟩ (by decide)
      (.int uint16Int))
    (hbase := by simpa [slot0F] using hbase)
    (her := by simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
        uint16St])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
  simpa [burnSlot0ObservationCardinalityValue, initState,
    slot0ObservationCardinalityWord, slot0SlotWord, solcSlotWord] using
    slot0StorageLocLoad_observationCardinality (initState cA gh bl σ σ₀ g A I)

theorem burnEvalSlot0ObservationCardinalityNext {v : PoolImmutables}
    {L : Store} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbase : L.get? "slot0" = none) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (slot0F "observationCardinalityNext")) =
      .ok (burnSlot0ObservationCardinalityNextValue σ I) := by
  rw [evalExpr_storage_scalar
    (t := .int uint16Int)
    (slot := slot0F "observationCardinalityNext")
    (er := { base := "slot0", steps := [.field "observationCardinalityNext"] })
    (loc := loc ⟨0⟩ ⟨27, by decide⟩ ⟨2, by decide⟩ (by decide)
      (.int uint16Int))
    (hbase := by simpa [slot0F] using hbase)
    (her := by simp [evalStorageRef, evalStorageRefStep, slot0F, EvalResult.bind, pure, bind])
    (hty := by
      simp [contract, storageDecls, storageTypeAt?, storageTypeStep?, slot0StructTy,
        uint16St])
    (hloc := by
      funext evm
      simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc])]
  simpa [burnSlot0ObservationCardinalityNextValue, initState,
    slot0ObservationCardinalityNextWord, slot0SlotWord, solcSlotWord] using
    slot0StorageLocLoad_observationCardinalityNext (initState cA gh bl σ σ₀ g A I)

theorem uniswapV3PoolModifyPositionSourceSlot0Loads {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      burnModifyPositionSlot0Prefix
      (ExecResult.ok (burnModifyPositionAfterSlot0Frame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnEvalSlot0SqrtPriceX96 (v := v)
      (L := burnModifyPositionStore I) (cA := cA) (gh := gh) (bl := bl)
      (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g)
      (by simp [burnModifyPositionStore]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnEvalSlot0Tick (v := v)
      (L := (burnModifyPositionStore I).insert "_slot0sqrtPriceX96"
        (burnSlot0SqrtPriceX96Value σ I))
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (by simp [burnModifyPositionStore]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnEvalSlot0ObservationIndex (v := v)
      (L := ((burnModifyPositionStore I)
        |>.insert "_slot0sqrtPriceX96" (burnSlot0SqrtPriceX96Value σ I))
        |>.insert "_slot0tick" (burnSlot0TickValue σ I))
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (by simp [burnModifyPositionStore]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnEvalSlot0ObservationCardinality (v := v)
      (L := (((burnModifyPositionStore I)
        |>.insert "_slot0sqrtPriceX96" (burnSlot0SqrtPriceX96Value σ I))
        |>.insert "_slot0tick" (burnSlot0TickValue σ I))
        |>.insert "_slot0observationIndex" (burnSlot0ObservationIndexValue σ I))
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (by simp [burnModifyPositionStore]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnEvalSlot0ObservationCardinalityNext (v := v)
      (L := ((((burnModifyPositionStore I)
        |>.insert "_slot0sqrtPriceX96" (burnSlot0SqrtPriceX96Value σ I))
        |>.insert "_slot0tick" (burnSlot0TickValue σ I))
        |>.insert "_slot0observationIndex" (burnSlot0ObservationIndexValue σ I))
        |>.insert "_slot0observationCardinality"
          (burnSlot0ObservationCardinalityValue σ I))
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (by simp [burnModifyPositionStore]))) ?_
  exact ExecBlock.nil

theorem uniswapV3PoolModifyPositionSourceThroughSlot0Loads {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper") ++
        burnModifyPositionSlot0Prefix)
      (ExecResult.ok (burnModifyPositionAfterSlot0Frame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolModifyPositionSourceThroughUpperLe (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge hle
  exact execBlock_append hprefix
    (uniswapV3PoolModifyPositionSourceSlot0Loads (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g))

theorem burnModifyPositionStore_owner (I : ExecutionEnv) :
    (burnModifyPositionStore I).get? "owner" = some (.address I.source) := by
  rw [burnModifyPositionStore]
  exact store_get_self
    ((((∅ : Store).insert "liquidityDelta" (burnLiquidityDeltaValue I))
      |>.insert "tickUpper" (burnTickUpperValue I))
      |>.insert "tickLower" (burnTickLowerValue I))
    "owner" (.address I.source)

theorem burnAfterSlot0Frame_owner {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterSlot0Frame v σ I).locals.get? "owner" =
      some (.address I.source) := by
  rw [burnModifyPositionAfterSlot0Frame]
  rw [store_get_ne5 (burnModifyPositionStore I)
    (k1 := "_slot0sqrtPriceX96") (k2 := "_slot0tick")
    (k3 := "_slot0observationIndex") (k4 := "_slot0observationCardinality")
    (k5 := "_slot0observationCardinalityNext") (a := "owner")
    (burnSlot0SqrtPriceX96Value σ I) (burnSlot0TickValue σ I)
    (burnSlot0ObservationIndexValue σ I) (burnSlot0ObservationCardinalityValue σ I)
    (burnSlot0ObservationCardinalityNextValue σ I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)]
  exact burnModifyPositionStore_owner I

theorem burnAfterSlot0Frame_tickLower {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterSlot0Frame v σ I).locals.get? "tickLower" =
      some (burnTickLowerValue I) := by
  rw [burnModifyPositionAfterSlot0Frame]
  rw [store_get_ne5 (burnModifyPositionStore I)
    (k1 := "_slot0sqrtPriceX96") (k2 := "_slot0tick")
    (k3 := "_slot0observationIndex") (k4 := "_slot0observationCardinality")
    (k5 := "_slot0observationCardinalityNext") (a := "tickLower")
    (burnSlot0SqrtPriceX96Value σ I) (burnSlot0TickValue σ I)
    (burnSlot0ObservationIndexValue σ I) (burnSlot0ObservationCardinalityValue σ I)
    (burnSlot0ObservationCardinalityNextValue σ I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)]
  exact burnModifyPositionStore_tickLower I

theorem burnAfterSlot0Frame_tickUpper {v : PoolImmutables} (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnModifyPositionAfterSlot0Frame v σ I).locals.get? "tickUpper" =
      some (burnTickUpperValue I) := by
  rw [burnModifyPositionAfterSlot0Frame]
  rw [store_get_ne5 (burnModifyPositionStore I)
    (k1 := "_slot0sqrtPriceX96") (k2 := "_slot0tick")
    (k3 := "_slot0observationIndex") (k4 := "_slot0observationCardinality")
    (k5 := "_slot0observationCardinalityNext") (a := "tickUpper")
    (burnSlot0SqrtPriceX96Value σ I) (burnSlot0TickValue σ I)
    (burnSlot0ObservationIndexValue σ I) (burnSlot0ObservationCardinalityValue σ I)
    (burnSlot0ObservationCardinalityNextValue σ I)
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)
    (by native_decide)]
  exact burnModifyPositionStore_tickUpper I

theorem burnEvalOwnerAfterSlot0 {v : PoolImmutables}
    {σ : AccountMap} {cA gh bl σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I) (.var "owner") = .ok (.address I.source) := by
  unfold evalExpr?
  rw [burnAfterSlot0Frame_owner]
  rfl

theorem burnEvalTickLowerAfterSlot0 {v : PoolImmutables}
    {σ : AccountMap} {cA gh bl σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I) (.var "tickLower") =
      .ok (burnTickLowerValue I) := by
  unfold evalExpr?
  rw [burnAfterSlot0Frame_tickLower]
  rfl

theorem burnEvalTickUpperAfterSlot0 {v : PoolImmutables}
    {σ : AccountMap} {cA gh bl σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I) (.var "tickUpper") =
      .ok (burnTickUpperValue I) := by
  unfold evalExpr?
  rw [burnAfterSlot0Frame_tickUpper]
  rfl

theorem burnEncodePackedTickLower (I : ExecutionEnv) :
    encodePackedValue? int24 (burnTickLowerValue I) =
      some ((EVM.wordOfInt (tickSpacingSint24Value (burnTickLowerWord I))).toBytesBE.drop 29) := by
  have hge : -↑(EVM.twoPow 23) ≤ tickSpacingSint24Value (burnTickLowerWord I) := by
    simpa [EVM.twoPow] using tickSpacingSint24Value_ge (burnTickLowerWord I)
  have hlt : tickSpacingSint24Value (burnTickLowerWord I) < ↑(EVM.twoPow 23) := by
    simpa [EVM.twoPow] using tickSpacingSint24Value_lt (burnTickLowerWord I)
  simp [encodePackedValue?, burnTickLowerValue, int24, int24Int, encodeABIWord?, hge, hlt]

theorem burnEncodePackedTickUpper (I : ExecutionEnv) :
    encodePackedValue? int24 (burnTickUpperValue I) =
      some ((EVM.wordOfInt (tickSpacingSint24Value (burnTickUpperWord I))).toBytesBE.drop 29) := by
  have hge : -↑(EVM.twoPow 23) ≤ tickSpacingSint24Value (burnTickUpperWord I) := by
    simpa [EVM.twoPow] using tickSpacingSint24Value_ge (burnTickUpperWord I)
  have hlt : tickSpacingSint24Value (burnTickUpperWord I) < ↑(EVM.twoPow 23) := by
    simpa [EVM.twoPow] using tickSpacingSint24Value_lt (burnTickUpperWord I)
  simp [encodePackedValue?, burnTickUpperValue, int24, int24Int, encodeABIWord?, hge, hlt]

theorem burnEvalPackedArgsTickUpper {v : PoolImmutables}
    {σ : AccountMap} {cA gh bl σ₀ A I} {g : Sat256} :
    evalPackedArgs? (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I) [(int24, .var "tickUpper")] =
      .ok ((EVM.wordOfInt (tickSpacingSint24Value (burnTickUpperWord I))).toBytesBE.drop 29) := by
  unfold evalPackedArgs?
  rw [burnEvalTickUpperAfterSlot0]
  simp only [EvalResult.bind, bind, pure, EvalResult.ofOption, burnEncodePackedTickUpper]
  unfold evalPackedArgs?
  simp only [List.append_nil]

theorem burnEvalPackedArgsTicks {v : PoolImmutables}
    {σ : AccountMap} {cA gh bl σ₀ A I} {g : Sat256} :
    evalPackedArgs? (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I) [(int24, .var "tickLower"), (int24, .var "tickUpper")] =
      .ok (((EVM.wordOfInt (tickSpacingSint24Value (burnTickLowerWord I))).toBytesBE.drop 29) ++
        ((EVM.wordOfInt (tickSpacingSint24Value (burnTickUpperWord I))).toBytesBE.drop 29)) := by
  unfold evalPackedArgs?
  rw [burnEvalTickLowerAfterSlot0]
  simp only [EvalResult.bind, bind, pure, EvalResult.ofOption, burnEncodePackedTickLower]
  rw [burnEvalPackedArgsTickUpper]

theorem burnEvalPackedPositionKeyArgs {v : PoolImmutables}
    {σ : AccountMap} {cA gh bl σ₀ A I} {g : Sat256} :
    evalPackedArgs? (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      [(addr, .var "owner"), (int24, .var "tickLower"), (int24, .var "tickUpper")] =
      .ok (burnPositionKeyPackedList I) := by
  unfold evalPackedArgs?
  rw [burnEvalOwnerAfterSlot0]
  simp only [EvalResult.bind, bind, pure, EvalResult.ofOption]
  simp [addr, encodePackedValue?, burnPositionKeyPackedList]
  rw [burnEvalPackedArgsTicks]

theorem burnEvalAbiEncodePackedPositionKey {v : PoolImmutables}
    {σ : AccountMap} {cA gh bl σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.abiEncodePacked [(addr, .var "owner"), (int24, .var "tickLower"),
        (int24, .var "tickUpper")]) =
      .ok (.bytes (burnPositionKeyPackedBytes I)) := by
  unfold evalExpr?
  rw [burnEvalPackedPositionKeyArgs]
  rfl

theorem burnEvalPositionKey {v : PoolImmutables}
    {σ : AccountMap} {cA gh bl σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (positionKey (.var "owner") (.var "tickLower") (.var "tickUpper")) =
      .ok (burnPositionKeyValue I) := by
  unfold positionKey
  unfold evalExpr?
  rw [burnEvalAbiEncodePackedPositionKey]
  rfl

theorem uniswapV3PoolModifyPositionSourcePositionKey {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecBlock (config v) (burnModifyPositionAfterSlot0Frame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      burnModifyPositionPositionKeyStep
      (ExecResult.ok (burnModifyPositionAfterPositionKeyFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  refine ExecBlock.consNormal (ExecStmt.letDecl (burnEvalPositionKey (v := v)
    (σ := σ) (cA := cA) (gh := gh) (bl := bl) (σ₀ := σ₀) (A := A)
    (I := I) (g := g))) ?_
  exact ExecBlock.nil

theorem uniswapV3PoolModifyPositionSourceThroughPositionKey {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper") ++
        burnModifyPositionSlot0Prefix ++ burnModifyPositionPositionKeyStep)
      (ExecResult.ok (burnModifyPositionAfterPositionKeyFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolModifyPositionSourceThroughSlot0Loads (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge hle
  exact execBlock_append hprefix
    (uniswapV3PoolModifyPositionSourcePositionKey (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g))

theorem burnEvalFeeGrowthGlobal0 {v : PoolImmutables}
    {L : Store} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbase : L.get? "feeGrowthGlobal0X128" = none) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I) (.storage feeGrowthGlobal0X128Ref) =
      .ok (burnFeeGrowthGlobal0Value σ I) := by
  apply evalExpr_storage_scalar_value
      (er := { base := "feeGrowthGlobal0X128", steps := [] })
      (t := .int uint256Int)
      (loc := loc ⟨1⟩ ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide)
        (.int uint256Int))
  · simpa [feeGrowthGlobal0X128Ref] using hbase
  · simp [evalStorageRef, feeGrowthGlobal0X128Ref, pure, bind, EvalResult.bind]
  · simp [contract, storageDecls, storageTypeAt?, uint256St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc]
  · simpa [burnFeeGrowthGlobal0Value, initState, solcSlotWord, loc, uint256Loc] using
      (storageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨1⟩)

theorem burnEvalFeeGrowthGlobal1 {v : PoolImmutables}
    {L : Store} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbase : L.get? "feeGrowthGlobal1X128" = none) :
    evalExpr? (config v) { contract := contract v, locals := L }
      (initState cA gh bl σ σ₀ g A I) (.storage feeGrowthGlobal1X128Ref) =
      .ok (burnFeeGrowthGlobal1Value σ I) := by
  apply evalExpr_storage_scalar_value
      (er := { base := "feeGrowthGlobal1X128", steps := [] })
      (t := .int uint256Int)
      (loc := loc ⟨2⟩ ⟨0, by decide⟩ ⟨32, by decide⟩ (by decide)
        (.int uint256Int))
  · simpa [feeGrowthGlobal1X128Ref] using hbase
  · simp [evalStorageRef, feeGrowthGlobal1X128Ref, pure, bind, EvalResult.bind]
  · simp [contract, storageDecls, storageTypeAt?, uint256St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout, loc]
  · simpa [burnFeeGrowthGlobal1Value, initState, solcSlotWord, loc, uint256Loc] using
      (storageLocLoad_uint256 (initState cA gh bl σ σ₀ g A I) ⟨2⟩)

theorem uniswapV3PoolModifyPositionSourceFeeGrowthGlobals {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    ExecBlock (config v) (burnModifyPositionAfterPositionKeyFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      burnModifyPositionFeeGrowthGlobalsStep
      (ExecResult.ok (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnEvalFeeGrowthGlobal0 (v := v)
      (L := (burnModifyPositionAfterPositionKeyFrame v σ I).locals)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (by
        simp [burnModifyPositionStore]))) ?_
  refine ExecBlock.consNormal
    (ExecStmt.letDecl (burnEvalFeeGrowthGlobal1 (v := v)
      (L := ((burnModifyPositionAfterPositionKeyFrame v σ I).locals
        |>.insert "_feeGrowthGlobal0X128" (burnFeeGrowthGlobal0Value σ I)))
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g)
      (by
        simp [burnModifyPositionStore]))) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (by
    change evalExpr? _ _ _ (.boolLit false) = .ok (.bool false)
    unfold evalExpr?
    rfl)) ?_
  refine ExecBlock.consNormal (ExecStmt.letDecl (by
    change evalExpr? _ _ _ (.boolLit false) = .ok (.bool false)
    unfold evalExpr?
    rfl)) ?_
  exact ExecBlock.nil

theorem uniswapV3PoolModifyPositionSourceThroughFeeGrowthGlobals {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hguard : uniswapV3PoolNoDelegateCallGuard v I ≠ ⟨0⟩)
    (htickLt :
      tickSpacingSint24Value (burnTickLowerWord I) <
        tickSpacingSint24Value (burnTickUpperWord I))
    (hge : ¬ tickSpacingSint24Value (burnTickLowerWord I) < (-887272 : Int))
    (hle : ¬ (887272 : Int) < tickSpacingSint24Value (burnTickUpperWord I)) :
    ExecBlock (config v) { contract := contract v, locals := burnModifyPositionStore I }
      (initState cA gh bl σ σ₀ g A I)
      (noDelegateCall v ++ checkTicksBody (.var "tickLower") (.var "tickUpper") ++
        burnModifyPositionSlot0Prefix ++ burnModifyPositionPositionKeyStep ++
        burnModifyPositionFeeGrowthGlobalsStep)
      (ExecResult.ok (burnModifyPositionAfterFeeGrowthGlobalsFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hprefix := uniswapV3PoolModifyPositionSourceThroughPositionKey (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g) hguard htickLt hge hle
  exact execBlock_append hprefix
    (uniswapV3PoolModifyPositionSourceFeeGrowthGlobals (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g))

noncomputable def burnModifyPositionSlot0Mem0 (I : ExecutionEnv) : ByteArray :=
  writeWord (burnModifyPositionMem4 I) 64 (UInt256.ofNat 480)

noncomputable def burnModifyPositionSlot0Mem1 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnModifyPositionSlot0Mem0 I) 256 (slot0SqrtPriceX96Word σ I)

noncomputable def burnModifyPositionSlot0Mem2 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnModifyPositionSlot0Mem1 σ I) 288 (slot0TickReturnWord σ I)

noncomputable def burnModifyPositionSlot0Mem3 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnModifyPositionSlot0Mem2 σ I) 320 (slot0ObservationIndexWord σ I)

noncomputable def burnModifyPositionSlot0Mem4 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnModifyPositionSlot0Mem3 σ I) 352 (slot0ObservationCardinalityWord σ I)

noncomputable def burnModifyPositionSlot0Mem5 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnModifyPositionSlot0Mem4 σ I) 384
    (slot0ObservationCardinalityNextWord σ I)

noncomputable def burnModifyPositionSlot0Mem6 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnModifyPositionSlot0Mem5 σ I) 416 (slot0FeeProtocolWord σ I)

noncomputable def burnModifyPositionSlot0Mem (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnModifyPositionSlot0Mem6 σ I) 448
    (slot0BoolReturnWord (slot0UnlockedRawWord σ I))

private theorem burnModifyPositionMem0_size_forSlot0 :
    burnModifyPositionMem0.size = 96 := by
  unfold burnModifyPositionMem0
  change ((UInt256.toByteArray (⟨256⟩ : UInt256)).write 0 solcFreePtrMem 64 32).size = 96
  exact toByteArray_write32_size_of_le solcFreePtrMem (⟨256⟩ : UInt256) 64 96 96
    solcFreePtrMem_size (by rw [solcFreePtrMem_size]; omega) (by omega)

private theorem burnModifyPositionMem1_size_forSlot0 (I : ExecutionEnv) :
    (burnModifyPositionMem1 I).size = 160 := by
  unfold burnModifyPositionMem1
  change (writeWord burnModifyPositionMem0 128 (UInt256.ofNat I.source.val)).size = 160
  rw [writeWord_size]
  · rw [burnModifyPositionMem0_size_forSlot0]
    omega
  · rw [burnModifyPositionMem0_size_forSlot0]
    native_decide

private theorem burnModifyPositionMem2_size_forSlot0 (I : ExecutionEnv) :
    (burnModifyPositionMem2 I).size = 192 := by
  unfold burnModifyPositionMem2
  change (writeWord (burnModifyPositionMem1 I) 160
    (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))).size = 192
  rw [writeWord_size]
  · rw [burnModifyPositionMem1_size_forSlot0 I]
    omega
  · rw [burnModifyPositionMem1_size_forSlot0 I]
    native_decide

private theorem burnModifyPositionMem3_size_forSlot0 (I : ExecutionEnv) :
    (burnModifyPositionMem3 I).size = 224 := by
  unfold burnModifyPositionMem3
  change (writeWord (burnModifyPositionMem2 I) 192
    (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))).size = 224
  rw [writeWord_size]
  · rw [burnModifyPositionMem2_size_forSlot0 I]
    omega
  · rw [burnModifyPositionMem2_size_forSlot0 I]
    native_decide

private theorem burnModifyPositionMem4_cascadeFromMem0_forSlot0 (I : ExecutionEnv) :
    burnModifyPositionMem4 I =
      writeCascade burnModifyPositionMem0
        [(128, UInt256.ofNat I.source.val),
         (160, UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)),
         (192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
         (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  rfl

private theorem burnModifyPositionMem4_cascadeFromMem1_forSlot0 (I : ExecutionEnv) :
    burnModifyPositionMem4 I =
      writeCascade (burnModifyPositionMem1 I)
        [(160, UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)),
         (192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
         (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  rfl

private theorem burnModifyPositionMem4_cascadeFromMem2_forSlot0 (I : ExecutionEnv) :
    burnModifyPositionMem4 I =
      writeCascade (burnModifyPositionMem2 I)
        [(192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
         (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  rfl

private theorem burnModifyPositionMem4_cascadeFromMem3_forSlot0 (I : ExecutionEnv) :
    burnModifyPositionMem4 I =
      writeCascade (burnModifyPositionMem3 I)
        [(224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))] := by
  rfl

theorem burnModifyPositionMem4_read128 (I : ExecutionEnv) :
    (burnModifyPositionMem4 I).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) := by
  rw [burnModifyPositionMem4_cascadeFromMem0_forSlot0]
  exact writeCascade_read_word_of_head_of_base burnModifyPositionMem0 (base := 96)
    (off := 128) (UInt256.ofNat I.source.val)
    [(160, UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)),
     (192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
     (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))]
    burnModifyPositionMem0_size_forSlot0 (by native_decide)
    (by
      simp [WindowDisjointFromWrites])

theorem burnModifyPositionMem4_read160 (I : ExecutionEnv) :
    (burnModifyPositionMem4 I).readWithPadding 160 32 =
      UInt256.toByteArray (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) := by
  rw [burnModifyPositionMem4_cascadeFromMem1_forSlot0]
  exact writeCascade_read_word_of_head_of_base (burnModifyPositionMem1 I) (base := 160)
    (off := 160) (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
    [(192, UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)),
     (224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))]
    (burnModifyPositionMem1_size_forSlot0 I) (by native_decide)
    (by
      simp [WindowDisjointFromWrites])

theorem burnModifyPositionMem4_read192 (I : ExecutionEnv) :
    (burnModifyPositionMem4 I).readWithPadding 192 32 =
      UInt256.toByteArray (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)) := by
  rw [burnModifyPositionMem4_cascadeFromMem2_forSlot0]
  exact writeCascade_read_word_of_head_of_base (burnModifyPositionMem2 I) (base := 192)
    (off := 192) (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
    [(224, UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))]
    (burnModifyPositionMem2_size_forSlot0 I) (by native_decide)
    (by
      simp [WindowDisjointFromWrites])

theorem burnModifyPositionMem4_read224 (I : ExecutionEnv) :
    (burnModifyPositionMem4 I).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  rw [burnModifyPositionMem4_cascadeFromMem3_forSlot0]
  exact writeCascade_read_word_of_head_of_base (burnModifyPositionMem3 I) (base := 224)
    (off := 224)
    (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) []
    (burnModifyPositionMem3_size_forSlot0 I) (by native_decide)
    (by simp [WindowDisjointFromWrites])

private def burnModifyPositionSlot0Writes (σ : AccountMap) (I : ExecutionEnv) :
    List (Nat × UInt256) :=
  [(64, UInt256.ofNat 480),
   (256, slot0SqrtPriceX96Word σ I),
   (288, slot0TickReturnWord σ I),
   (320, slot0ObservationIndexWord σ I),
   (352, slot0ObservationCardinalityWord σ I),
   (384, slot0ObservationCardinalityNextWord σ I),
   (416, slot0FeeProtocolWord σ I),
   (448, slot0BoolReturnWord (slot0UnlockedRawWord σ I))]

private theorem burnModifyPositionSlot0Mem_cascade (σ : AccountMap) (I : ExecutionEnv) :
    burnModifyPositionSlot0Mem σ I =
      writeCascade (burnModifyPositionMem4 I) (burnModifyPositionSlot0Writes σ I) := by
  rfl

theorem burnModifyPositionSlot0Mem_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionSlot0Mem σ I).size = 480 := by
  rw [burnModifyPositionSlot0Mem_cascade]
  exact writeCascade_size_of_base (burnModifyPositionMem4 I)
    (burnModifyPositionSlot0Writes σ I) (burnModifyPositionMem4_size I)
    (by
      simp [burnModifyPositionSlot0Writes, WriteGapsOk])
    (by simp [burnModifyPositionSlot0Writes, writeCascadeSize])

private theorem burnModifyPositionSlot0Mem_readPreserved
    (σ : AccountMap) (I : ExecutionEnv) {off : Nat}
    (hdisj :
      WindowDisjointFromWrites 256 off 32 (burnModifyPositionSlot0Writes σ I)) :
    (burnModifyPositionSlot0Mem σ I).readWithPadding off 32 =
      (burnModifyPositionMem4 I).readWithPadding off 32 := by
  rw [burnModifyPositionSlot0Mem_cascade]
  exact writeCascade_read_preserved_of_base (burnModifyPositionMem4 I)
    (burnModifyPositionSlot0Writes σ I) (base := 256) (read := off)
    (burnModifyPositionMem4_size I) hdisj

theorem burnModifyPositionSlot0Mem_read128 (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionSlot0Mem σ I).readWithPadding 128 32 =
      UInt256.toByteArray (UInt256.ofNat I.source.val) := by
  rw [burnModifyPositionSlot0Mem_readPreserved σ I
    (by
      simp [burnModifyPositionSlot0Writes, WindowDisjointFromWrites])]
  exact burnModifyPositionMem4_read128 I

theorem burnModifyPositionSlot0Mem_read160 (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionSlot0Mem σ I).readWithPadding 160 32 =
      UInt256.toByteArray (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I)) := by
  rw [burnModifyPositionSlot0Mem_readPreserved σ I
    (by
      simp [burnModifyPositionSlot0Writes, WindowDisjointFromWrites])]
  exact burnModifyPositionMem4_read160 I

theorem burnModifyPositionSlot0Mem_read192 (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionSlot0Mem σ I).readWithPadding 192 32 =
      UInt256.toByteArray (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I)) := by
  rw [burnModifyPositionSlot0Mem_readPreserved σ I
    (by
      simp [burnModifyPositionSlot0Writes, WindowDisjointFromWrites])]
  exact burnModifyPositionMem4_read192 I

theorem burnModifyPositionSlot0Mem_read224 (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionSlot0Mem σ I).readWithPadding 224 32 =
      UInt256.toByteArray
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I))) := by
  rw [burnModifyPositionSlot0Mem_readPreserved σ I
    (by
      simp [burnModifyPositionSlot0Writes, WindowDisjointFromWrites])]
  exact burnModifyPositionMem4_read224 I

theorem burnModifyPositionSlot0Mem_mload128 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨128⟩ : UInt256).toNat ≥ (burnModifyPositionSlot0Mem σ I).size
        ∨ (⟨128⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnModifyPositionSlot0Mem σ I).readWithPadding (⟨128⟩ : UInt256).toNat 32))) =
      UInt256.ofNat I.source.val := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnModifyPositionSlot0Mem σ I) (aw := UInt256.ofNat 15)
    (off := ⟨128⟩) (v := UInt256.ofNat I.source.val)
    (by rw [burnModifyPositionSlot0Mem_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨128⟩ : UInt256).toNat = 128 from by decide]
        using burnModifyPositionSlot0Mem_read128 σ I)

theorem burnModifyPositionSlot0Mem_mload160 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨160⟩ : UInt256).toNat ≥ (burnModifyPositionSlot0Mem σ I).size
        ∨ (⟨160⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnModifyPositionSlot0Mem σ I).readWithPadding (⟨160⟩ : UInt256).toNat 32))) =
      UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnModifyPositionSlot0Mem σ I) (aw := UInt256.ofNat 15)
    (off := ⟨160⟩)
    (v := UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))
    (by rw [burnModifyPositionSlot0Mem_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨160⟩ : UInt256).toNat = 160 from by decide]
        using burnModifyPositionSlot0Mem_read160 σ I)

theorem burnModifyPositionSlot0Mem_mload192 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨192⟩ : UInt256).toNat ≥ (burnModifyPositionSlot0Mem σ I).size
        ∨ (⟨192⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnModifyPositionSlot0Mem σ I).readWithPadding (⟨192⟩ : UInt256).toNat 32))) =
      UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnModifyPositionSlot0Mem σ I) (aw := UInt256.ofNat 15)
    (off := ⟨192⟩)
    (v := UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))
    (by rw [burnModifyPositionSlot0Mem_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨192⟩ : UInt256).toNat = 192 from by decide]
        using burnModifyPositionSlot0Mem_read192 σ I)

theorem burnModifyPositionSlot0Mem_mload224 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨224⟩ : UInt256).toNat ≥ (burnModifyPositionSlot0Mem σ I).size
        ∨ (⟨224⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnModifyPositionSlot0Mem σ I).readWithPadding (⟨224⟩ : UInt256).toNat 32))) =
      UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)) := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnModifyPositionSlot0Mem σ I) (aw := UInt256.ofNat 15)
    (off := ⟨224⟩)
    (v := UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord I)))
    (by rw [burnModifyPositionSlot0Mem_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨224⟩ : UInt256).toNat = 224 from by decide]
        using burnModifyPositionSlot0Mem_read224 σ I)

theorem burnModifyPositionSlot0Mem_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (burnModifyPositionSlot0Mem σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 480) := by
  rw [burnModifyPositionSlot0Mem_cascade]
  exact writeCascade_read_word_of_head_of_base (burnModifyPositionMem4 I)
    (base := 256) (off := 64) (UInt256.ofNat 480)
    [(256, slot0SqrtPriceX96Word σ I),
     (288, slot0TickReturnWord σ I),
     (320, slot0ObservationIndexWord σ I),
     (352, slot0ObservationCardinalityWord σ I),
     (384, slot0ObservationCardinalityNextWord σ I),
     (416, slot0FeeProtocolWord σ I),
     (448, slot0BoolReturnWord (slot0UnlockedRawWord σ I))]
    (burnModifyPositionMem4_size I) (by native_decide)
    (by simp [WindowDisjointFromWrites])

theorem burnModifyPositionSlot0Mem_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnModifyPositionSlot0Mem σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 15 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnModifyPositionSlot0Mem σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      UInt256.ofNat 480 := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnModifyPositionSlot0Mem σ I) (aw := UInt256.ofNat 15)
    (off := ⟨64⟩) (v := UInt256.ofNat 480)
    (by rw [burnModifyPositionSlot0Mem_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnModifyPositionSlot0Mem_read64 σ I)

theorem twoWordHashMem_read0_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 32 =
      UInt256.toByteArray key := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      native_decide
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_below _ _ 32 0 (by rw [toByteArray_size])
      (by rw [hword0Size]; omega) (by omega)]
  unfold wordAt0Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size]) (by omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray key).size ≤ 32
    rw [toByteArray_size])
theorem twoWordHashMem_read32_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 32 32 =
      UInt256.toByteArray slot := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      native_decide
  unfold twoWordHashMem wordAt32Mem
  rw [write32_read_back _ _ _ (by rw [toByteArray_size])
      (by rw [hword0Size]; omega)]
  apply ByteArray.ext
  rw [ByteArray.data_extract]
  exact Array.extract_eq_self_of_le (by
    change (UInt256.toByteArray slot).size ≤ 32
    rw [toByteArray_size])
theorem twoWordHashMem_size_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).size = mem.size := by
  have hword0Size : (wordAt0Mem key mem).size = mem.size := by
    unfold wordAt0Mem
    change (writeWord mem 0 key).size = mem.size
    rw [writeWord_size]
    · omega
    · have hzero : 0 - mem.size = 0 := by omega
      rw [hzero]
      native_decide
  unfold twoWordHashMem wordAt32Mem
  change (writeWord (wordAt0Mem key mem) 32 slot).size = mem.size
  rw [writeWord_size]
  · rw [hword0Size]
    omega
  · rw [hword0Size]
    have hzero : 32 - mem.size = 0 := by omega
    rw [hzero]
    native_decide
theorem twoWordHashMem_read0_64_of_size_ge {mem : ByteArray} (key slot : UInt256)
    (hmem : 64 ≤ mem.size) :
    (twoWordHashMem key slot mem).readWithPadding 0 64 =
      UInt256.toByteArray key ++ UInt256.toByteArray slot := by
  have hsize := twoWordHashMem_size_of_size_ge (mem := mem) key slot hmem
  rw [readWithPadding_eq_extract' _ 0 64 (by norm_num) (by norm_num)
      (by rw [hsize]; omega)]
  have hleft :
      (twoWordHashMem key slot mem).extract 0 32 = UInt256.toByteArray key := by
    rw [← readWithPadding_eq_extract _ 0 (by rw [hsize]; omega),
      twoWordHashMem_read0_of_size_ge key slot hmem]
  have hright :
      (twoWordHashMem key slot mem).extract 32 64 = UInt256.toByteArray slot := by
    rw [← readWithPadding_eq_extract _ 32 (by rw [hsize]; omega),
      twoWordHashMem_read32_of_size_ge key slot hmem]
  rw [show (twoWordHashMem key slot mem).extract 0 64 =
      (twoWordHashMem key slot mem).extract 0 32 ++
        (twoWordHashMem key slot mem).extract 32 64 by
      rw [ByteArray.extract_append_extract]
      norm_num]
  rw [hleft, hright]
theorem twoWordHashMem_solcMappingSlot_of_size_ge
    (baseSlot key : UInt256) {mem : ByteArray} (hmem : 64 ≤ mem.size) :
    UInt256.ofNat (fromByteArrayBigEndian
        (ffi.KEC ((twoWordHashMem key baseSlot mem).readWithPadding 0 64))) =
      solcMappingSlot baseSlot key := by
  rw [twoWordHashMem_read0_64_of_size_ge key baseSlot hmem]
  unfold solcMappingSlot
  exact mappingSlot_single key baseSlot
abbrev burnPositionKeyOwnerPackedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.lnot (⟨79228162514264337593543950335⟩ : UInt256))
    (UInt256.shiftLeft (UInt256.ofNat I.source.val) ⟨96⟩)
abbrev burnPositionKeyLowerPackedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.signextend ⟨2⟩
      (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord I))) ⟨232⟩
abbrev burnPositionKeyUpperPackedWord (I : ExecutionEnv) : UInt256 :=
  UInt256.shiftLeft
    (UInt256.signextend ⟨2⟩
      (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord I))) ⟨232⟩
abbrev burnPositionKeyPackedLengthWord : UInt256 :=
  (⟨26⟩ : UInt256) + UInt256.sub (UInt256.ofNat 480) (UInt256.ofNat 480)
abbrev burnPositionKeyNewFreePtrWord : UInt256 :=
  UInt256.ofNat 480 + (⟨58⟩ : UInt256)
theorem burnPositionKeyPackedLengthWord_eq :
    burnPositionKeyPackedLengthWord = (⟨26⟩ : UInt256) := by
  native_decide
theorem burnPositionKeyNewFreePtrWord_eq :
    burnPositionKeyNewFreePtrWord = UInt256.ofNat 538 := by
  native_decide
noncomputable def burnPositionKeyMem0 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnModifyPositionSlot0Mem σ I) 512 (burnPositionKeyOwnerPackedWord I)
noncomputable def burnPositionKeyMem1 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnPositionKeyMem0 σ I) 532 (burnPositionKeyLowerPackedWord I)
noncomputable def burnPositionKeyMem2 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnPositionKeyMem1 σ I) 535 (burnPositionKeyUpperPackedWord I)
noncomputable def burnPositionKeyMem3 (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnPositionKeyMem2 σ I) 480 burnPositionKeyPackedLengthWord
noncomputable def burnPositionKeyPackedHashMem (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  writeWord (burnPositionKeyMem3 σ I) 64 burnPositionKeyNewFreePtrWord
noncomputable abbrev burnPositionKeyHashWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.ofNat (fromByteArrayBigEndian
    (ffi.KEC ((burnPositionKeyPackedHashMem σ I).readWithPadding 512 26)))
noncomputable abbrev burnPositionBaseSlotWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcMappingSlot ⟨7⟩ (burnPositionKeyHashWord σ I)
noncomputable abbrev burnPositionKeyMappingMem (σ : AccountMap) (I : ExecutionEnv) :
    ByteArray :=
  twoWordHashMem (burnPositionKeyHashWord σ I) ⟨7⟩
    (burnPositionKeyPackedHashMem σ I)
private def burnPositionKeyPackedWrites (I : ExecutionEnv) : List (Nat × UInt256) :=
  [(512, burnPositionKeyOwnerPackedWord I),
   (532, burnPositionKeyLowerPackedWord I),
   (535, burnPositionKeyUpperPackedWord I)]
private theorem burnPositionKeyMem2_cascade (σ : AccountMap) (I : ExecutionEnv) :
    burnPositionKeyMem2 σ I =
      writeCascade (burnModifyPositionSlot0Mem σ I)
        (burnPositionKeyPackedWrites I) := by
  rfl

theorem burnPositionKeyMem2_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem2 σ I).size = 567 := by
  rw [burnPositionKeyMem2_cascade]
  exact writeCascade_size_of_base (burnModifyPositionSlot0Mem σ I)
    (burnPositionKeyPackedWrites I) (burnModifyPositionSlot0Mem_size σ I)
    (by
      simp [burnPositionKeyPackedWrites, WriteGapsOk]
      native_decide)
    (by simp [burnPositionKeyPackedWrites, writeCascadeSize])

theorem burnPositionKeyMem2_read64 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem2 σ I).readWithPadding 64 32 =
      UInt256.toByteArray (UInt256.ofNat 480) := by
  rw [burnPositionKeyMem2_cascade]
  rw [writeCascade_read_preserved_of_base (burnModifyPositionSlot0Mem σ I)
    (burnPositionKeyPackedWrites I) (base := 480) (read := 64)
    (burnModifyPositionSlot0Mem_size σ I)
    (by
      simp [burnPositionKeyPackedWrites, WindowDisjointFromWrites]
      native_decide)]
  exact burnModifyPositionSlot0Mem_read64 σ I

theorem burnPositionKeyMem2_mload64 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨64⟩ : UInt256).toNat ≥ (burnPositionKeyMem2 σ I).size
        ∨ (⟨64⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnPositionKeyMem2 σ I).readWithPadding (⟨64⟩ : UInt256).toNat 32))) =
      UInt256.ofNat 480 := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionKeyMem2 σ I) (aw := UInt256.ofNat 18)
    (off := ⟨64⟩) (v := UInt256.ofNat 480)
    (by rw [burnPositionKeyMem2_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨64⟩ : UInt256).toNat = 64 from by decide]
        using burnPositionKeyMem2_read64 σ I)

theorem burnPositionKeyMem3_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem3 σ I).size = 567 := by
  unfold burnPositionKeyMem3
  rw [writeWord_size]
  · rw [burnPositionKeyMem2_size σ I]
    omega
  · rw [burnPositionKeyMem2_size σ I]
    native_decide

theorem burnPositionKeyPackedHashMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyPackedHashMem σ I).size = 567 := by
  unfold burnPositionKeyPackedHashMem
  rw [writeWord_size]
  · rw [burnPositionKeyMem3_size σ I]
    omega
  · rw [burnPositionKeyMem3_size σ I]
    native_decide

theorem burnPositionKeyMem3_read480 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyMem3 σ I).readWithPadding 480 32 =
      UInt256.toByteArray burnPositionKeyPackedLengthWord := by
  unfold burnPositionKeyMem3
  exact writeWord_read_back (burnPositionKeyMem2 σ I) 480
    burnPositionKeyPackedLengthWord
    (by rw [burnPositionKeyMem2_size σ I]; native_decide)

theorem burnPositionKeyPackedHashMem_read480 (σ : AccountMap) (I : ExecutionEnv) :
    (burnPositionKeyPackedHashMem σ I).readWithPadding 480 32 =
      UInt256.toByteArray burnPositionKeyPackedLengthWord := by
  unfold burnPositionKeyPackedHashMem
  rw [writeWord_read_preserved (burnPositionKeyMem3 σ I) 64 480
    burnPositionKeyNewFreePtrWord
    (by rw [burnPositionKeyMem3_size σ I]; native_decide)
    (by rw [burnPositionKeyMem3_size σ I]; omega)]
  exact burnPositionKeyMem3_read480 σ I

theorem burnPositionKeyPackedHashMem_mload480 (σ : AccountMap) (I : ExecutionEnv) :
    (if (⟨480⟩ : UInt256).toNat ≥ (burnPositionKeyPackedHashMem σ I).size
        ∨ (⟨480⟩ : UInt256) ≥ UInt256.ofNat 18 * ⟨32⟩ then ⟨0⟩
     else UInt256.ofNat
       (fromByteArrayBigEndian
        ((burnPositionKeyPackedHashMem σ I).readWithPadding
          (⟨480⟩ : UInt256).toNat 32))) =
      burnPositionKeyPackedLengthWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnPositionKeyPackedHashMem σ I) (aw := UInt256.ofNat 18)
    (off := ⟨480⟩) (v := burnPositionKeyPackedLengthWord)
    (by rw [burnPositionKeyPackedHashMem_size σ I]; native_decide)
    (by native_decide)
    (by
      simpa [show (⟨480⟩ : UInt256).toNat = 480 from by decide]
        using burnPositionKeyPackedHashMem_read480 σ I)

private theorem uniswapV3PoolBurnAfterCheckTicksPatchDisjoint33 {v : PoolImmutables}
    {pc : UInt256}
    (hlo : 16264 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals omega

private theorem uniswapV3PoolBurnAfterCheckTicksDecodeEqTemplate {v : PoolImmutables}
    {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 16264 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 19295 ≤ uniswapV3PoolBytecode.size := by native_decide
      omega)
    (uniswapV3PoolBurnAfterCheckTicksPatchDisjoint33 (v := v) (pc := pc) hlo hhi)

private theorem uniswapV3PoolPatchPreservesJumpDest19151 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨19151⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched19151 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨19151⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest19151

private theorem uniswapV3PoolPatchPreservesJumpDest16867 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨16867⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched16867 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨16867⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest16867

private theorem uniswapV3PoolPatchPreservesJumpDest19166 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨19166⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolJumpDestPatched19166 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨19166⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest19166

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnAfterCheckTicksSlot0Frame {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16264⟩
      (⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionMem4 ee) (UInt256.ofNat 8) rdata (cA, σ) k C)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨16397⟩
      (⟨32⟩ :: slot0TickReturnWord σ ee :: ⟨96⟩ :: ⟨256⟩ :: ⟨64⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionSlot0Mem σ ee) (UInt256.ofNat 15) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 16264 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnAfterCheckTicksDecodeEqTemplate hpatch
      hlo hhi
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask := by
    native_decide
  have hmask16 : (⟨65535⟩ : UInt256) = slot0Uint16Mask := by
    native_decide
  have hmask8 : (⟨255⟩ : UInt256) = slot0Uint8Mask := by
    native_decide
  have hshift160 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩ = slot0ShiftBytes 20 := by
    native_decide
  have hshift184 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨184⟩ = slot0ShiftBytes 23 := by
    native_decide
  have hshift200 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨200⟩ = slot0ShiftBytes 25 := by
    native_decide
  have hshift216 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨216⟩ = slot0ShiftBytes 27 := by
    native_decide
  have hshift232 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨232⟩ = slot0ShiftBytes 29 := by
    native_decide
  have hshift240 :
      UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨240⟩ = slot0ShiftBytes 30 := by
    native_decide
  have rd16268 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov)]
  have rd16269 := by
    simpa [burnModifyPositionFreePtrLoad] using
      rd16268.mload 0 (UInt256.ofNat 256) (UInt256.ofNat 8)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost
        (by simpa [burnModifyPositionFreePtrLoad] using burnModifyPositionFreePtrLoad_eq ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16275 := evm_run rd16269 with [
    raw push1 ⟨224⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw mstore 0 (burnModifyPositionSlot0Mem0 ee) (UInt256.ofNat 8)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost rfl
      (by native_decide) (by evm_ov)]
  have rd16277 := evm_run rd16275 with [
    raw push1 ⟨0⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov)]
  obtain ⟨k16278, C16278, rd16278Raw⟩ := rd16277.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16278 := by
    simpa [slot0SlotWord, solcSlotWord] using rd16278Raw
  have rd16301 := evm_run rd16278 with [
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw and (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw mstore 3 (burnModifyPositionSlot0Mem1 σ ee) (UInt256.ofNat 9)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        rw [hmask160]
        rfl)
      (by native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw div (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov)]
  have rd16302 := RD.signextend rd16301
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16303 := evm_run rd16302 with [
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov)]
  have rd16304 := RD.signextend rd16303
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16305 := evm_run rd16304 with [
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov)]
  have rd16306 := RD.signextend rd16305
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16314 := evm_run rd16306 with [
    raw push1 ⟨32⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw mstore 3 (burnModifyPositionSlot0Mem2 σ ee) (UInt256.ofNat 10)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnModifyPositionSlot0Mem2 slot0TickReturnWord slot0SlotWord solcSlotWord
        rw [hshift160, slot0SignextendTwo_idempotent, slot0SignextendTwo_idempotent]
        simp only [show (UInt256.ofNat 256 + (⟨32⟩ : UInt256)).toNat = 288 from by decide]
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16330 := evm_run rd16314 with [
    raw push2 ⟨65535⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨184⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw div (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw and (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw mstore 3 (burnModifyPositionSlot0Mem3 σ ee) (UInt256.ofNat 11)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnModifyPositionSlot0Mem3 slot0ObservationIndexWord slot0SlotWord solcSlotWord
        rw [hmask16, hshift184, u256_land_comm slot0Uint16Mask]
        simp only [show ((⟨64⟩ : UInt256) + UInt256.ofNat 256).toNat = 320 from by decide]
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16348 := evm_run rd16330 with [
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨200⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw div (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw and (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨96⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw mstore 3 (burnModifyPositionSlot0Mem4 σ ee) (UInt256.ofNat 12)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnModifyPositionSlot0Mem4 slot0ObservationCardinalityWord slot0SlotWord solcSlotWord
        rw [hmask16, hshift200, u256_land_comm slot0Uint16Mask]
        simp only [show (UInt256.ofNat 256 + (⟨96⟩ : UInt256)).toNat = 352 from by decide]
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16363 := evm_run rd16348 with [
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨216⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw div (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw and (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup7 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw mstore 3 (burnModifyPositionSlot0Mem5 σ ee) (UInt256.ofNat 13)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnModifyPositionSlot0Mem5 slot0ObservationCardinalityNextWord slot0SlotWord
          solcSlotWord
        rw [hmask16, hshift216, u256_land_comm slot0Uint16Mask]
        simp only [show (UInt256.ofNat 256 + (⟨128⟩ : UInt256)).toNat = 384 from by decide]
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16379 := evm_run rd16363 with [
    raw push1 ⟨255⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨232⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw div (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw and (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw mstore 3 (burnModifyPositionSlot0Mem6 σ ee) (UInt256.ofNat 14)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnModifyPositionSlot0Mem6 slot0FeeProtocolWord slot0SlotWord solcSlotWord
        rw [hmask8, hshift232, u256_land_comm slot0Uint8Mask]
        simp only [show (UInt256.ofNat 256 + (⟨160⟩ : UInt256)).toNat = 416 from by decide]
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16397 := evm_run rd16379 with [
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨240⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw div (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw and (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw iszero (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw iszero (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw dup6 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) (by evm_ov),
    raw mstore 3 (burnModifyPositionSlot0Mem σ ee) (UInt256.ofNat 15)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnModifyPositionSlot0Mem slot0UnlockedRawWord slot0BoolReturnWord slot0SlotWord
          solcSlotWord
        rw [hmask8, hshift240, u256_land_comm slot0Uint8Mask]
        simp only [show (UInt256.ofNat 256 + (⟨192⟩ : UInt256)).toNat = 448 from by decide]
        rfl)
      (by native_decide) (by evm_ov)]
  exact ⟨_, _, by
    simpa [slot0TickReturnWord, slot0SlotWord, solcSlotWord, hshift160,
      slot0SignextendTwo_idempotent] using rd16397⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnAfterCheckTicksEnterPositionKey {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16397⟩
      (⟨32⟩ :: slot0TickReturnWord σ ee :: ⟨96⟩ :: ⟨256⟩ :: ⟨64⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionSlot0Mem σ ee) (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hov : R.length + 35 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨19151⟩
      (slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionSlot0Mem σ ee) (UInt256.ofNat 15) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 16264 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnAfterCheckTicksDecodeEqTemplate hpatch
      hlo hhi
  have rd16398 := evm_run h with [
    raw dup9 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16399 := by
    simpa using
      rd16398.mload 0 (UInt256.ofNat ee.source.val) (UInt256.ofNat 15)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (burnModifyPositionSlot0Mem_mload128 σ ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16402 := evm_run rd16399 with [
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup10 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16403 := by
    simpa [show ((⟨128⟩ : UInt256) + ⟨32⟩) = (⟨160⟩ : UInt256) from by decide,
      show ((⟨32⟩ : UInt256) + ⟨128⟩) = (⟨160⟩ : UInt256) from by decide] using
      rd16402.mload 0 (UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee))
        (UInt256.ofNat 15)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (burnModifyPositionSlot0Mem_mload160 σ ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16406 := evm_run rd16403 with [
    raw swap5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup10 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16407 := by
    simpa [show ((⟨128⟩ : UInt256) + ⟨64⟩) = (⟨192⟩ : UInt256) from by decide,
      show ((⟨64⟩ : UInt256) + ⟨128⟩) = (⟨192⟩ : UInt256) from by decide] using
      rd16406.mload 0 (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee))
        (UInt256.ofNat 15)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (burnModifyPositionSlot0Mem_mload192 σ ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16410 := evm_run rd16407 with [
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup10 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16411 := by
    simpa [show ((⟨128⟩ : UInt256) + ⟨96⟩) = (⟨224⟩ : UInt256) from by decide,
      show ((⟨96⟩ : UInt256) + ⟨128⟩) = (⟨224⟩ : UInt256) from by decide] using
      rd16410.mload 0
        (UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)))
        (UInt256.ofNat 15)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (burnModifyPositionSlot0Mem_mload224 σ ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16427 := evm_run rd16411 with [
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨16428⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨19151⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, by
    simpa using rd16427.jump
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (uniswapV3PoolJumpDestPatched19151 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnAfterCheckTicksCallPositionKeyRoutine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨19151⟩
      (slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionSlot0Mem σ ee) (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hov : R.length + 40 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨16867⟩
      (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨7⟩ :: ⟨19166⟩ :: ⟨0⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionSlot0Mem σ ee) (UInt256.ofNat 15) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 16264 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnAfterCheckTicksDecodeEqTemplate hpatch
      hlo hhi
  have rd19165 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨19166⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨7⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨16867⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, by
    simpa using rd19165.jump
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (uniswapV3PoolJumpDestPatched16867 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnAfterCheckTicksPositionKeyRoutine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨16867⟩
      (UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨7⟩ :: ⟨19166⟩ :: ⟨0⟩ ::
        slot0TickReturnWord σ ee ::
        UInt256.signextend ⟨15⟩ (UInt256.sub ⟨0⟩ (burnAmountCleanWord ee)) ::
        UInt256.signextend ⟨2⟩ (burnTickUpperCleanWord ee) ::
        UInt256.signextend ⟨2⟩ (burnTickLowerCleanWord ee) ::
        UInt256.ofNat ee.source.val :: ⟨16428⟩ :: ⟨256⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨128⟩ :: ⟨9737⟩ ::
        ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        burnAmountCleanWord ee :: burnTickUpperCleanWord ee :: burnTickLowerCleanWord ee ::
        ret :: R)
      (burnModifyPositionSlot0Mem σ ee) (UInt256.ofNat 15) rdata (cA, σ) k C)
    (hov : R.length + 55 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨19166⟩
      (burnPositionBaseSlotWord σ ee :: ⟨0⟩ ::
        slot0TickReturnWord σ ee ::
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
      (hlo : 16264 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnAfterCheckTicksDecodeEqTemplate hpatch
      hlo hhi
  have hd16878 :
      decode code ⟨16878⟩ =
        some (.Push .PUSH12, some (⟨79228162514264337593543950335⟩, 12)) := by
    rw [hdec _ (by native_decide) (by native_decide)]
    native_decide
  have hpackedStart :
      (⟨32⟩ : UInt256) + UInt256.ofNat 480 = ⟨512⟩ := by
    native_decide
  have hpackedStartRev :
      UInt256.ofNat 480 + (⟨32⟩ : UInt256) = ⟨512⟩ := by
    native_decide
  have hnewFree :
      UInt256.ofNat 480 + (⟨58⟩ : UInt256) = burnPositionKeyNewFreePtrWord := rfl
  have hslot :
      UInt256.ofNat (fromByteArrayBigEndian
          (ffi.KEC ((burnPositionKeyMappingMem σ ee).readWithPadding 0 64))) =
        burnPositionBaseSlotWord σ ee := by
    exact twoWordHashMem_solcMappingSlot_of_size_ge ⟨7⟩
      (burnPositionKeyHashWord σ ee)
      (by rw [burnPositionKeyPackedHashMem_size σ ee]; omega)
  have rd16871 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨64⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16872 := by
    simpa using
      rd16871.mload 0 (UInt256.ofNat 480) (UInt256.ofNat 15)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (burnModifyPositionSlot0Mem_mload64 σ ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16878pre := evm_run rd16872 with [
    raw push1 ⟨96⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16891 := by
    simpa using
      rd16878pre.pushConst (⟨79228162514264337593543950335⟩ : UInt256)
        (by native_decide : Operation.POp.PUSH12 ≠ .PUSH0) hd16878
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16901 := evm_run rd16891 with [
    raw not (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw and (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨32⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup7 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mstore 6 (burnPositionKeyMem0 σ ee) (UInt256.ofNat 17)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnPositionKeyMem0 burnPositionKeyOwnerPackedWord
        rw [hpackedStartRev]
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16906pre := evm_run rd16901 with [
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16907pre := RD.signextend rd16906pre
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16916 := evm_run rd16907pre with [
    raw push1 ⟨232⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨52⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mstore 3 (burnPositionKeyMem1 σ ee) (UInt256.ofNat 18)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnPositionKeyMem1 burnPositionKeyLowerPackedWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16920pre := evm_run rd16916 with [
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16921pre := RD.signextend rd16920pre
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16928 := evm_run rd16921pre with [
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw shl (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨55⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mstore 0 (burnPositionKeyMem2 σ ee) (UInt256.ofNat 18)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnPositionKeyMem2 burnPositionKeyUpperPackedWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16930pre := evm_run rd16928 with [
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16930 := by
    simpa using
      rd16930pre.mload 0 (UInt256.ofNat 480) (UInt256.ofNat 18)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (burnPositionKeyMem2_mload64 σ ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16938 := evm_run rd16930 with [
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup5 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw sub (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨26⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mstore 0 (burnPositionKeyMem3 σ ee) (UInt256.ofNat 18)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnPositionKeyMem3 burnPositionKeyPackedLengthWord
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16945 := evm_run rd16938 with [
    raw push1 ⟨58⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap4 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mstore 0 (burnPositionKeyPackedHashMem σ ee) (UInt256.ofNat 18)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnPositionKeyPackedHashMem
        rw [hnewFree]
        rfl)
      (by native_decide) (by evm_ov)]
  have rd16947pre := evm_run rd16945 with [
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16947 := by
    simpa [burnPositionKeyPackedLengthWord_eq] using
      rd16947pre.mload 0 burnPositionKeyPackedLengthWord (UInt256.ofNat 18)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost (burnPositionKeyPackedHashMem_mload480 σ ee)
        (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16953 := evm_run rd16947 with [
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw add (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16954 := by
    simpa [hpackedStart, burnPositionKeyHashWord] using
      rd16953.keccak256 0 (burnPositionKeyHashWord σ ee)
        (UInt256.ofNat 18)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost rfl (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16959 := evm_run rd16954 with [
    raw push1 ⟨0⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mstore 0
      (wordAt0Mem (burnPositionKeyHashWord σ ee) (burnPositionKeyPackedHashMem σ ee))
      (UInt256.ofNat 18)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost rfl
      (by native_decide) (by evm_ov)]
  have rd16964pre := evm_run rd16959 with [
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw mstore 0 (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18)
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide) mem_cost
      (by
        unfold burnPositionKeyMappingMem twoWordHashMem
        rfl)
      (by native_decide) (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd16965 := by
    simpa [burnPositionBaseSlotWord] using
      rd16964pre.keccak256 0 (burnPositionBaseSlotWord σ ee)
        (UInt256.ofNat 18)
        (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
        mem_cost hslot (by native_decide)
        (by simp only [List.length_cons] at hov ⊢; omega)
  have rd16966 := evm_run rd16965 with [
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, by
    simpa using rd16966.jump
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (uniswapV3PoolJumpDestPatched19166 hpatch)
      (by simp only [List.length_cons] at hov ⊢; omega)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolBurnAfterCheckTicksFeeGlobalsBranchTest {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {ret : UInt256} {R : List UInt256}
    {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨19166⟩
      (burnPositionBaseSlotWord σ ee :: ⟨0⟩ ::
        slot0TickReturnWord σ ee ::
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
    ∃ k' C', RD code ee g s0 ⟨19189⟩
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
      (burnPositionKeyMappingMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k' C' := by
  have hdec (pc : UInt256)
      (hlo : 16264 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 19295) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    exact uniswapV3PoolBurnAfterCheckTicksDecodeEqTemplate hpatch
      hlo hhi
  have rd19167 := evm_run h with [
    raw jumpdest (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd19169 := evm_run rd19167 with [
    raw push1 ⟨1⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd19170⟩ := rd19169.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd19172 := evm_run rd19170 with [
    raw push1 ⟨2⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  obtain ⟨_, _, rd19173⟩ := rd19172.sload
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd19184pre := evm_run rd19173 with [
    raw swap2 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap3 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw pop (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨0⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push1 ⟨15⟩ (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw dup8 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw swap1 (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  have rd19185 := RD.signextend rd19184pre
    (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
    (by simp only [List.length_cons] at hov ⊢; omega)
  have rd19189 := evm_run rd19185 with [
    raw iszero (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov),
    raw push2 ⟨19492⟩
      (by rw [hdec _ (by native_decide) (by native_decide)]; native_decide)
      (by evm_ov)]
  exact ⟨_, _, by simpa [solcSlotWord] using rd19189⟩

end Benchmarks.UniswapV3Pool
