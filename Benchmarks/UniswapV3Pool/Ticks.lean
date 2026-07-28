import Benchmarks.UniswapV3Pool.Uint128
import Benchmarks.UniswapV3Pool.ObservationsInt56
import Benchmarks.UniswapV3Pool.TicksInt128
import Benchmarks.UniswapV3Pool.TicksReturnMemory
import Reasoning.MemCascade

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach

namespace Benchmarks.UniswapV3Pool

abbrev ticksArgWord (I : ExecutionEnv) : UInt256 :=
  calldataWord I.calldata 4

abbrev ticksArgCleanWord (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨2⟩ (ticksArgWord I)

abbrev ticksArgValue (I : ExecutionEnv) : Value :=
  .int (tickSpacingSint24Value (ticksArgWord I))

abbrev ticksArgKey (I : ExecutionEnv) : KeyValue :=
  .int (tickSpacingSint24Value (ticksArgWord I))

abbrev ticksStore (I : ExecutionEnv) : Store :=
  (∅ : Store).insert "arg0" (ticksArgValue I)

abbrev ticksBaseSlot (I : ExecutionEnv) : UInt256 :=
  ticksBase (ticksArgKey I)

abbrev ticksPacked3Slot (I : ExecutionEnv) : UInt256 :=
  ticksBaseSlot I + ⟨3⟩

abbrev ticksShiftBytes (n : Nat) : UInt256 :=
  UInt256.ofNat (256 ^ n)

abbrev ticksUint32Mask : UInt256 :=
  UInt256.ofNat (2 ^ 32 - 1)

theorem ticksUint32Mask_toNat :
    ticksUint32Mask.toNat = 2 ^ 32 - 1 := by
  exact ulit_toNat' _ (by norm_num [UInt256.size])

theorem ticksUint32Mask_bound (w : UInt256) :
    (UInt256.land w ticksUint32Mask).toNat < EVM.twoPow 32 := by
  rw [uland_toNat]
  rw [ticksUint32Mask_toNat]
  exact lt_of_le_of_lt (nat_land_le_right _ _) (by norm_num [EVM.twoPow])

theorem ticksUint32Mask_clean {w : UInt256} (hcanon : w.toNat < EVM.twoPow 32) :
    UInt256.land w ticksUint32Mask = w := by
  apply u256_inj
  show Nat.land w.toNat ticksUint32Mask.toNat % EVM.twoPow 256 = w.toNat
  rw [ticksUint32Mask_toNat, nat_land_mask_eq_mod]
  rw [show EVM.twoPow 32 = 2 ^ 32 from rfl] at hcanon
  rw [Nat.mod_eq_of_lt hcanon]
  exact Nat.mod_eq_of_lt w.val.isLt

abbrev ticksPacked0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (ticksBaseSlot I)

abbrev ticksLiquidityGrossWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (ticksPacked0Word σ I) uint128Mask

abbrev ticksLiquidityNetRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (ticksPacked0Word σ I) (ticksShiftBytes 16)

abbrev ticksLiquidityNetStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (ticksLiquidityNetRawWord σ I) uint128Mask

abbrev ticksLiquidityNetReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨15⟩ (ticksLiquidityNetRawWord σ I)

abbrev ticksFeeGrowthOutside0Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (ticksBaseSlot I + ⟨1⟩)

abbrev ticksFeeGrowthOutside1Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (ticksBaseSlot I + ⟨2⟩)

abbrev ticksPacked3Word (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (ticksPacked3Slot I)

abbrev ticksTickCumulativeRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 0)

abbrev ticksTickCumulativeStorageWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (ticksTickCumulativeRawWord σ I) observationsUint56Mask

abbrev ticksTickCumulativeReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.signextend ⟨6⟩ (ticksPacked3Word σ I)

abbrev ticksSecondsPerLiquidityWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 7)) slot0Uint160Mask

abbrev ticksSecondsOutsideWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 27))
    ticksUint32Mask

abbrev ticksInitializedRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 31)) slot0Uint8Mask

abbrev ticksInitializedReturnWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  slot0BoolReturnWord (ticksInitializedRawWord σ I)

abbrev ticksReturnValues (σ : AccountMap) (I : ExecutionEnv) : List Value :=
  [ .int (Int.ofNat (ticksLiquidityGrossWord σ I).toNat),
    wordToElem (.int int128Int) (ticksLiquidityNetStorageWord σ I),
    .int (Int.ofNat (ticksFeeGrowthOutside0Word σ I).toNat),
    .int (Int.ofNat (ticksFeeGrowthOutside1Word σ I).toNat),
    wordToElem (.int int56Int) (ticksTickCumulativeStorageWord σ I),
    .int (Int.ofNat (ticksSecondsPerLiquidityWord σ I).toNat),
    .int (Int.ofNat (ticksSecondsOutsideWord σ I).toNat),
    wordToElem .bool (ticksInitializedRawWord σ I) ]

theorem ticksArgKeyWord (I : ExecutionEnv) :
    keyValueToWord (ticksArgKey I) = ticksArgCleanWord I := by
  unfold ticksArgKey ticksArgCleanWord ticksArgWord keyValueToWord
  exact wordOfInt_sint24Value_eq_signextend_two (calldataWord I.calldata 4)

theorem ticksBaseSlot_eq_solcMappingSlot (I : ExecutionEnv) :
    ticksBaseSlot I = solcMappingSlot ⟨5⟩ (ticksArgCleanWord I) := by
  unfold ticksBaseSlot ticksBase mapSlot solcMappingSlot
  rw [ticksArgKeyWord I]

theorem decodeScalarWordsWithMode_int24_ok {bytes : List UInt8}
    (hlen0 : (bytes.take 32).length = 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int24] bytes 0 =
      some [Value.int (tickSpacingSint24Value (ABI.bytesToWord (bytes.take 32)))] := by
  simp only [decodeScalarWordsWithMode?]
  unfold decodeScalarWordWithMode? readWord? readBytes? int24 int24Int tickSpacingSint24Value
  simp only [List.drop_zero]
  rw [if_pos hlen0]
  simp only [Option.bind, bind]
  unfold decodeABIWord?
  simp only [OfNat.ofNat_ne_zero, ↓reduceIte]
  rfl

theorem decodeScalarWordsWithMode_int24_none_short {bytes : List UInt8}
    (hshort : bytes.length < 32) :
    decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int24] bytes 0 = none := by
  simp only [decodeScalarWordsWithMode?]
  have htake0n : ¬ (bytes.take 32).length = 32 := by
    rw [List.length_take]
    omega
  unfold decodeScalarWordWithMode? readWord? readBytes? int24 int24Int
  simp only [List.drop_zero]
  rw [if_neg htake0n]
  simp only [Option.bind, bind]

theorem uniswapV3PoolTicksDecodeOk {v : PoolImmutables} {I : ExecutionEnv}
    (hsz36 : 36 ≤ I.calldata.size) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (ticksTransition.params.map Param.name)
      (transitionSignature ticksTransition).paramTypes I.calldata = some (ticksStore I) := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  have htake4 : ((I.calldata.toList.drop 4).take 32).length = 32 := by
    rw [List.length_take, List.length_drop, htlen]
    omega
  have hword4 : ABI.bytesToWord ((I.calldata.toList.drop 4).take 32) =
      calldataWord I.calldata 4 :=
    decode_word_at_eq I.calldata 4 (by omega) (by norm_num)
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := ticksTransition.params.map Param.name)
    (types := (transitionSignature ticksTransition).paramTypes) (cd := I.calldata)]
  · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
    change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int24]
        (I.calldata.toList.drop 4) 0 with
      | some values => decodeCalldata.insertValues ["arg0"] values ∅
      | none => none) = some (ticksStore I)
    rw [decodeScalarWordsWithMode_int24_ok (bytes := I.calldata.toList.drop 4) htake4]
    change decodeCalldata.insertValues ["arg0"]
        [Value.int
          (tickSpacingSint24Value
            (ABI.bytesToWord ((I.calldata.toList.drop 4).take 32)))] ∅ =
      some (ticksStore I)
    simp [decodeCalldata.insertValues, ticksStore, ticksArgValue, ticksArgWord]
    rw [hword4]
  · native_decide

theorem uniswapV3PoolTicksDecodeShort {v : PoolImmutables} {I : ExecutionEnv}
    (hshort : I.calldata.size < 36) :
    decodeCalldataWithMode (config v).abiDecodeMode
      (ticksTransition.params.map Param.name)
      (transitionSignature ticksTransition).paramTypes I.calldata = none := by
  have htlen : I.calldata.toList.length = I.calldata.size := by
    rw [byteArray_toList_eq, Array.length_toList]
    rfl
  rw [show (config v).abiDecodeMode = DecodeMode.legacySolc05 from rfl]
  rw [decodeCalldataWithMode_legacyScalarWords_eq
    (names := ticksTransition.params.map Param.name)
    (types := (transitionSignature ticksTransition).paramTypes) (cd := I.calldata)]
  · by_cases hsz4 : I.calldata.size < 4
    · rw [if_pos (by rw [htlen]; omega : I.calldata.toList.length < 4)]
    · rw [if_neg (by rw [htlen]; omega : ¬ I.calldata.toList.length < 4)]
      change (match decodeScalarWordsWithMode? DecodeMode.legacySolc05 [int24]
          (I.calldata.toList.drop 4) 0 with
        | some values => decodeCalldata.insertValues ["arg0"] values ∅
        | none => none) = none
      rw [decodeScalarWordsWithMode_int24_none_short
        (bytes := I.calldata.toList.drop 4) (by rw [List.length_drop, htlen]; omega)]
  · native_decide

set_option maxHeartbeats 1000000 in
theorem uniswapV3PoolDispatch_ticks {v : PoolImmutables} {cd : ByteArray}
    (hsel : (uniswapV3PoolSelBytes 24 == cd.extract 0 4) = true) :
    dispatchMsg (contract v) cd = some ticksTransition := by
  apply dispatchMsg_eq_some_of_split
    (pre := [burnTransition, collectTransition v, collectprotocolTransition v, factoryTransition v,
      feeTransition v, feegrowthglobal0X128Transition, feegrowthglobal1X128Transition,
      flashTransition v, increaseobservationcardinalitynextTransition v, initializeTransition,
      liquidityTransition, maxliquiditypertickTransition v, mintTransition v,
      observationsTransition, observeTransition v, positionsTransition, protocolfeesTransition,
      setfeeprotocolTransition v, slot0Transition, snapshotcumulativesinsideTransition v,
      swapTransition v, tickbitmapTransition, tickspacingTransition v])
    (post := [token0Transition v, token1Transition v])
  · simp [contract, transitions]
  · intro t ht
    simp at ht
    rcases ht with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · rw [selectorOf, burnSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 17) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, collectSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 10) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, collectProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 15) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, factorySelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 19) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, feeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 22) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal0X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 23) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, feeGrowthGlobal1X128SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 8) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, flashSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 9) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, increaseObservationCardinalityNextSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 5) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, initializeSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 25) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, liquiditySelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 2) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, maxLiquidityPerTickSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 13) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, mintSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 7) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, observationsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 4) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, observeSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 16) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, positionsSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 11) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, protocolFeesSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 3) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, setFeeProtocolSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 14) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, slot0SelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 6) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, snapshotCumulativesInsideSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 18) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, swapSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 1) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, tickBitmapSelectorBytes]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 12) (j := 24)
          (by native_decide) hsel
    · rw [selectorOf, tickSpacingSelectorBytes v]
      simpa [uniswapV3PoolSelBytes] using
        uniswapV3PoolSelectorMissOfHitBytes (cd := cd) (i := 20) (j := 24)
          (by native_decide) hsel
  · rw [selectorOf, ticksSelectorBytes]
    simpa [uniswapV3PoolSelBytes] using hsel

theorem ticksStore_arg0 (I : ExecutionEnv) :
    Std.HashMap.get? (ticksStore I) "arg0" = some (ticksArgValue I) := by
  simp [ticksStore]

theorem evalExpr_ticks_arg0 {v : PoolImmutables} (evm : EVM.State) (I : ExecutionEnv) :
    evalExpr? (config v) { contract := contract v, locals := ticksStore I } evm
      (.var "arg0") = .ok (ticksArgValue I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [ticksStore_arg0]

def ticksEvaledRef (I : ExecutionEnv) (field : Ident) : EvaledStorageRef :=
  { base := "ticks", steps := [.mindex (ticksArgKey I), .field field] }

theorem evalStorageRef_ticks {v : PoolImmutables} (evm : EVM.State)
    (I : ExecutionEnv) (field : Ident) :
    evalStorageRef (config v) { contract := contract v, locals := ticksStore I } evm
      (ticksF (.var "arg0") field) = .ok (ticksEvaledRef I field) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, ticksF,
    ticksEvaledRef, evalExpr_ticks_arg0, ticksArgValue, ticksArgKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem ticksStorageLocLoad_liquidityGross (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (ticksBaseSlot I) ⟨0, by decide⟩ ⟨16, by decide⟩ (by decide)
          (.int uint128Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ticksBaseSlot I))
        uint128Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 16) - 1) = uint128Mask by native_decide]
  simpa [loc, uint128Int] using
    storageLocLoad_uint_offset0 evm (ticksBaseSlot I) (16 : Fin 33) ⟨128, by decide⟩
      (hbound := by decide) (by decide)

theorem ticksStorageLocLoad_liquidityNet (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (ticksBaseSlot I) ⟨16, by decide⟩ ⟨16, by decide⟩ (by decide)
          (.int int128Int)) =
      wordToElem (.int int128Int)
        (UInt256.land
          (UInt256.div
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ticksBaseSlot I))
            (ticksShiftBytes 16))
          uint128Mask) := by
  rw [← show UInt256.ofNat (256 ^ (16 : Nat)) = ticksShiftBytes 16 by rfl]
  rw [← show UInt256.ofNat (256 ^ (16 : Nat) - 1) = uint128Mask by native_decide]
  simpa [loc, int128Int] using
    storageLocLoad_sint_offset evm (ticksBaseSlot I) (16 : Fin 32) (16 : Fin 33)
      ⟨128, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem ticksStorageLocLoad_feeGrowthOutside0 (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (ticksBaseSlot I + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
          (by decide) (.int uint256Int)) =
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (ticksBaseSlot I + ⟨1⟩)).toNat) := by
  simpa [loc, uint256Loc] using storageLocLoad_uint256 evm (ticksBaseSlot I + ⟨1⟩)

theorem ticksStorageLocLoad_feeGrowthOutside1 (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (ticksBaseSlot I + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
          (by decide) (.int uint256Int)) =
      .int (Int.ofNat
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner
          (ticksBaseSlot I + ⟨2⟩)).toNat) := by
  simpa [loc, uint256Loc] using storageLocLoad_uint256 evm (ticksBaseSlot I + ⟨2⟩)

theorem ticksStorageLocLoad_tickCumulativeOutside (evm : EVM.State)
    (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (ticksPacked3Slot I) ⟨0, by decide⟩ ⟨7, by decide⟩
          (by decide) (.int int56Int)) =
      wordToElem (.int int56Int)
        (UInt256.land
          (UInt256.div
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ticksPacked3Slot I))
            (ticksShiftBytes 0))
          observationsUint56Mask) := by
  rw [← show UInt256.ofNat (256 ^ (0 : Nat)) = ticksShiftBytes 0 by rfl]
  rw [← show UInt256.ofNat (256 ^ (7 : Nat) - 1) = observationsUint56Mask by
    native_decide]
  simpa [loc, int56Int] using
    storageLocLoad_sint_offset evm (ticksPacked3Slot I) (0 : Fin 32) (7 : Fin 33)
      ⟨56, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem ticksStorageLocLoad_secondsPerLiquidity (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (ticksPacked3Slot I) ⟨7, by decide⟩ ⟨20, by decide⟩
          (by decide) (.int uint160Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ticksPacked3Slot I))
          (ticksShiftBytes 7))
        slot0Uint160Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ (7 : Nat)) = ticksShiftBytes 7 by rfl]
  rw [← show UInt256.ofNat (256 ^ (20 : Nat) - 1) = slot0Uint160Mask by native_decide]
  simpa [loc, uint160Int] using
    storageLocLoad_uint_offset evm (ticksPacked3Slot I) (7 : Fin 32) (20 : Fin 33)
      ⟨160, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem ticksStorageLocLoad_secondsOutside (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (ticksPacked3Slot I) ⟨27, by decide⟩ ⟨4, by decide⟩
          (by decide) (.int uint32Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ticksPacked3Slot I))
          (ticksShiftBytes 27))
        ticksUint32Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ (27 : Nat)) = ticksShiftBytes 27 by rfl]
  rw [← show UInt256.ofNat (256 ^ (4 : Nat) - 1) = ticksUint32Mask by native_decide]
  simpa [loc, uint32Int] using
    storageLocLoad_uint_offset evm (ticksPacked3Slot I) (27 : Fin 32) (4 : Fin 33)
      ⟨32, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem ticksStorageLocLoad_initialized (evm : EVM.State) (I : ExecutionEnv) :
    storageLocLoad evm
        (loc (ticksPacked3Slot I) ⟨31, by decide⟩ ⟨1, by decide⟩
          (by decide) .bool) =
      wordToElem .bool
        (UInt256.land
          (UInt256.div
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner (ticksPacked3Slot I))
            (ticksShiftBytes 31))
          slot0Uint8Mask) := by
  rw [← show UInt256.ofNat (256 ^ (31 : Nat)) = ticksShiftBytes 31 by rfl]
  simpa [loc] using
    storageLocLoad_bool_offset evm (ticksPacked3Slot I) (31 : Fin 32)
      (hbound := by decide) (by decide)

theorem uniswapV3PoolTicksSourceBody {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hwv : I.weiValue = ⟨0⟩) :
    ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (ticksStore I) ticksTransition.body
      (.returned { contract := contract v, locals := ticksStore I }
        (initState cA gh bl σ σ₀ g A I)
        (some (ticksReturnValues σ I))) := by
  change ExecTransitionBody (config v) (contract v)
      (initState cA gh bl σ σ₀ g A I) (ticksStore I)
      [ .require (.binary .eq (.env .callvalue) (.intLit 0)),
        .return [ .storage (ticksF (.var "arg0") "liquidityGross"),
          .storage (ticksF (.var "arg0") "liquidityNet"),
          .storage (ticksF (.var "arg0") "feeGrowthOutside0X128"),
          .storage (ticksF (.var "arg0") "feeGrowthOutside1X128"),
          .storage (ticksF (.var "arg0") "tickCumulativeOutside"),
          .storage (ticksF (.var "arg0") "secondsPerLiquidityOutsideX128"),
          .storage (ticksF (.var "arg0") "secondsOutside"),
          .storage (ticksF (.var "arg0") "initialized") ] ] _
  exact ExecFuncBody.execBlockRet <|
    ExecBlock.consNormal (ExecStmt.requireTrue (evalCallvalueEq_true (by simp [initState, hwv]))) <|
      ExecBlock.consReturn <| ExecStmt.return (by
        have hgross :
            evalExpr? (config v) { contract := contract v, locals := ticksStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (ticksF (.var "arg0") "liquidityGross")) =
            .ok (.int (Int.ofNat (ticksLiquidityGrossWord σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := ticksEvaledRef I "liquidityGross")
              (t := .int uint128Int)
              (loc := loc (ticksBaseSlot I) ⟨0, by decide⟩ ⟨16, by decide⟩
                (by decide) (.int uint128Int))
          · simp [ticksStore, ticksF]
          · exact evalStorageRef_ticks (v := v) (initState cA gh bl σ σ₀ g A I) I
              "liquidityGross"
          · simp [ticksEvaledRef, contract, storageDecls, storageTypeAt?, storageTypeStep?,
              tickInfoStructTy, uint128St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              ticksEvaledRef, ticksBaseSlot, loc]
          · simpa [initState, ticksLiquidityGrossWord, ticksPacked0Word, solcSlotWord] using
              ticksStorageLocLoad_liquidityGross (initState cA gh bl σ σ₀ g A I) I
        have hnet :
            evalExpr? (config v) { contract := contract v, locals := ticksStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (ticksF (.var "arg0") "liquidityNet")) =
            .ok (wordToElem (.int int128Int) (ticksLiquidityNetStorageWord σ I)) := by
          apply evalExpr_storage_scalar_value
              (er := ticksEvaledRef I "liquidityNet")
              (t := .int int128Int)
              (loc := loc (ticksBaseSlot I) ⟨16, by decide⟩ ⟨16, by decide⟩
                (by decide) (.int int128Int))
          · simp [ticksStore, ticksF]
          · exact evalStorageRef_ticks (v := v) (initState cA gh bl σ σ₀ g A I) I
              "liquidityNet"
          · simp [ticksEvaledRef, contract, storageDecls, storageTypeAt?, storageTypeStep?,
              tickInfoStructTy, int128St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              ticksEvaledRef, ticksBaseSlot, loc]
          · simpa [initState, ticksLiquidityNetStorageWord, ticksLiquidityNetRawWord,
              ticksPacked0Word, solcSlotWord] using
              ticksStorageLocLoad_liquidityNet (initState cA gh bl σ σ₀ g A I) I
        have hfee0 :
            evalExpr? (config v) { contract := contract v, locals := ticksStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (ticksF (.var "arg0") "feeGrowthOutside0X128")) =
            .ok (.int (Int.ofNat (ticksFeeGrowthOutside0Word σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := ticksEvaledRef I "feeGrowthOutside0X128")
              (t := .int uint256Int)
              (loc := loc (ticksBaseSlot I + ⟨1⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
                (by decide) (.int uint256Int))
          · simp [ticksStore, ticksF]
          · exact evalStorageRef_ticks (v := v) (initState cA gh bl σ σ₀ g A I) I
              "feeGrowthOutside0X128"
          · simp [ticksEvaledRef, contract, storageDecls, storageTypeAt?, storageTypeStep?,
              tickInfoStructTy, uint256St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              ticksEvaledRef, ticksBaseSlot, loc]
          · simpa [initState, ticksFeeGrowthOutside0Word, solcSlotWord] using
              ticksStorageLocLoad_feeGrowthOutside0 (initState cA gh bl σ σ₀ g A I) I
        have hfee1 :
            evalExpr? (config v) { contract := contract v, locals := ticksStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (ticksF (.var "arg0") "feeGrowthOutside1X128")) =
            .ok (.int (Int.ofNat (ticksFeeGrowthOutside1Word σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := ticksEvaledRef I "feeGrowthOutside1X128")
              (t := .int uint256Int)
              (loc := loc (ticksBaseSlot I + ⟨2⟩) ⟨0, by decide⟩ ⟨32, by decide⟩
                (by decide) (.int uint256Int))
          · simp [ticksStore, ticksF]
          · exact evalStorageRef_ticks (v := v) (initState cA gh bl σ σ₀ g A I) I
              "feeGrowthOutside1X128"
          · simp [ticksEvaledRef, contract, storageDecls, storageTypeAt?, storageTypeStep?,
              tickInfoStructTy, uint256St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              ticksEvaledRef, ticksBaseSlot, loc]
          · simpa [initState, ticksFeeGrowthOutside1Word, solcSlotWord] using
              ticksStorageLocLoad_feeGrowthOutside1 (initState cA gh bl σ σ₀ g A I) I
        have htick :
            evalExpr? (config v) { contract := contract v, locals := ticksStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (ticksF (.var "arg0") "tickCumulativeOutside")) =
            .ok (wordToElem (.int int56Int) (ticksTickCumulativeStorageWord σ I)) := by
          apply evalExpr_storage_scalar_value
              (er := ticksEvaledRef I "tickCumulativeOutside")
              (t := .int int56Int)
              (loc := loc (ticksPacked3Slot I) ⟨0, by decide⟩ ⟨7, by decide⟩
                (by decide) (.int int56Int))
          · simp [ticksStore, ticksF]
          · exact evalStorageRef_ticks (v := v) (initState cA gh bl σ σ₀ g A I) I
              "tickCumulativeOutside"
          · simp [ticksEvaledRef, contract, storageDecls, storageTypeAt?, storageTypeStep?,
              tickInfoStructTy, int56St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              ticksEvaledRef, ticksBaseSlot, ticksPacked3Slot, loc]
          · simpa [initState, ticksTickCumulativeStorageWord, ticksTickCumulativeRawWord,
        ticksPacked3Word, solcSlotWord] using
              ticksStorageLocLoad_tickCumulativeOutside (initState cA gh bl σ σ₀ g A I) I
        have hsecondsLiq :
            evalExpr? (config v) { contract := contract v, locals := ticksStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (ticksF (.var "arg0") "secondsPerLiquidityOutsideX128")) =
            .ok (.int (Int.ofNat (ticksSecondsPerLiquidityWord σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := ticksEvaledRef I "secondsPerLiquidityOutsideX128")
              (t := .int uint160Int)
              (loc := loc (ticksPacked3Slot I) ⟨7, by decide⟩ ⟨20, by decide⟩
                (by decide) (.int uint160Int))
          · simp [ticksStore, ticksF]
          · exact evalStorageRef_ticks (v := v) (initState cA gh bl σ σ₀ g A I) I
              "secondsPerLiquidityOutsideX128"
          · simp [ticksEvaledRef, contract, storageDecls, storageTypeAt?, storageTypeStep?,
              tickInfoStructTy, uint160St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              ticksEvaledRef, ticksBaseSlot, ticksPacked3Slot, loc]
          · simpa [initState, ticksSecondsPerLiquidityWord, ticksPacked3Word,
              solcSlotWord] using
              ticksStorageLocLoad_secondsPerLiquidity (initState cA gh bl σ σ₀ g A I) I
        have hsecondsOut :
            evalExpr? (config v) { contract := contract v, locals := ticksStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (ticksF (.var "arg0") "secondsOutside")) =
            .ok (.int (Int.ofNat (ticksSecondsOutsideWord σ I).toNat)) := by
          apply evalExpr_storage_scalar_value
              (er := ticksEvaledRef I "secondsOutside")
              (t := .int uint32Int)
              (loc := loc (ticksPacked3Slot I) ⟨27, by decide⟩ ⟨4, by decide⟩
                (by decide) (.int uint32Int))
          · simp [ticksStore, ticksF]
          · exact evalStorageRef_ticks (v := v) (initState cA gh bl σ σ₀ g A I) I
              "secondsOutside"
          · simp [ticksEvaledRef, contract, storageDecls, storageTypeAt?, storageTypeStep?,
              tickInfoStructTy, uint32St]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              ticksEvaledRef, ticksBaseSlot, ticksPacked3Slot, loc]
          · simpa [initState, ticksSecondsOutsideWord, ticksPacked3Word, solcSlotWord] using
              ticksStorageLocLoad_secondsOutside (initState cA gh bl σ σ₀ g A I) I
        have hinit :
            evalExpr? (config v) { contract := contract v, locals := ticksStore I }
              (initState cA gh bl σ σ₀ g A I)
              (.storage (ticksF (.var "arg0") "initialized")) =
            .ok (wordToElem .bool (ticksInitializedRawWord σ I)) := by
          apply evalExpr_storage_scalar_value
              (er := ticksEvaledRef I "initialized")
              (t := .bool)
              (loc := loc (ticksPacked3Slot I) ⟨31, by decide⟩ ⟨1, by decide⟩
                (by decide) .bool)
          · simp [ticksStore, ticksF]
          · exact evalStorageRef_ticks (v := v) (initState cA gh bl σ σ₀ g A I) I
              "initialized"
          · simp [ticksEvaledRef, contract, storageDecls, storageTypeAt?, storageTypeStep?,
              tickInfoStructTy, boolSt]
          · funext evm
            simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
              ticksEvaledRef, ticksBaseSlot, ticksPacked3Slot, loc]
          · simpa [initState, ticksInitializedRawWord, ticksPacked3Word, solcSlotWord] using
              ticksStorageLocLoad_initialized (initState cA gh bl σ σ₀ g A I) I
        simp only [ticksReturnValues, Solm.evalExprs?.eq_def, hgross, hnet, hfee0, hfee1,
          htick, hsecondsLiq, hsecondsOut, hinit, EvalResult.bind, bind, pure])

theorem uniswapV3PoolTicksValueTransport {σ_evm σ_solm : AccountMap} {I : ExecutionEnv}
    (hAccounts : accountMapEquiv σ_evm σ_solm) :
    some (ticksReturnValues σ_solm I) = some (ticksReturnValues σ_evm I) := by
  have hbase := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (ticksBaseSlot I) (⟨0⟩ : UInt256)
  have hfee0 := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (ticksBaseSlot I + ⟨1⟩) (⟨0⟩ : UInt256)
  have hfee1 := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (ticksBaseSlot I + ⟨2⟩) (⟨0⟩ : UInt256)
  have hpacked3 := accountMapEquiv_storage_findD hAccounts I.codeOwner
    (ticksPacked3Slot I) (⟨0⟩ : UInt256)
  dsimp [ticksReturnValues, ticksLiquidityGrossWord, ticksLiquidityNetStorageWord,
    ticksLiquidityNetRawWord, ticksFeeGrowthOutside0Word, ticksFeeGrowthOutside1Word,
    ticksTickCumulativeStorageWord, ticksTickCumulativeRawWord,
    ticksSecondsPerLiquidityWord, ticksSecondsOutsideWord, ticksInitializedRawWord,
    ticksPacked0Word, ticksPacked3Word, solcSlotWord]
  rw [← hbase, ← hfee0, ← hfee1, ← hpacked3]

private def ticksStSignextend (s : State) (res : UInt256) (t : List UInt256) : State :=
  { s with
      machineState.stack := res :: t,
      machineState.gasAvailable := s.machineState.gasAvailable.subNat 5
      machineState.pc := s.machineState.pc + ⟨1⟩
      machineState.execLength := s.machineState.execLength + 1 }

private theorem ticksSignextendXstep {code : ByteArray} {s : State} {pc a b : UInt256}
    {t : List UInt256}
    (hcode : s.executionEnv.code = code) (hpc : s.machineState.pc = pc)
    (hdec : decode code pc = some (.SIGNEXTEND, .none))
    (hstk : s.machineState.stack = a :: b :: t) (hov : t.length + 1 ≤ 1024) :
    Xstep (D_J code 0) s =
      if s.machineState.gasAvailable.toNat < 5 then .error .OutOfGass
      else .ok (ticksStSignextend s (UInt256.signextend a b) t, .none) := by
  have hdecS : decode s.executionEnv.code s.machineState.pc = some (.SIGNEXTEND, .none) := by
    rw [hcode, hpc]
    exact hdec
  have hstep := step_signextend s hdecS
  have hnoOverflow : ¬ 1024 ≤ t.length := by omega
  simpa [hcode, hstk, GasConstants.Glow, ticksStSignextend, hnoOverflow] using hstep

private theorem ticksRDSignextend {code : ByteArray} {ee : ExecutionEnv}
    {g : Sat256} {s0 : State} {pc : UInt256} {mem : ByteArray}
    {aw : UInt256} {rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap} {k C : ℕ}
    {a b : UInt256} {t : List UInt256}
    (h : RD code ee g s0 pc (a :: b :: t) mem aw rdata acc k C)
    (hdec : decode code pc = some (.SIGNEXTEND, .none)) (hov : t.length + 1 ≤ 1024) :
    RD code ee g s0 (pc + ⟨1⟩) (UInt256.signextend a b :: t) mem aw rdata acc
      (k + 1) (C + 5) := by
  unfold RD at h ⊢
  rcases h with hoog | ⟨s, hX, hcode, hpc, hstk, hgas, hk, hC, hmem, haw, hrdata, hacc, hee,
      hworld⟩
  · exact Or.inl hoog
  · have st := ticksSignextendXstep hcode hpc hdec hstk hov
    by_cases gg : g.toNat < C + 5
    · exact Or.inl (hX.trans (stepOOG hgas st hk hC (by omega)))
    · refine Or.inr ⟨ticksStSignextend s (UInt256.signextend a b) t,
        hX.trans (stepContinue hgas st hk (Nat.not_lt.mp gg)), ?_, ?_, ?_, ?_, by omega,
        by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · simp only [ticksStSignextend]; exact hcode
      · simp only [ticksStSignextend]; rw [hpc]
      · rfl
      · simp only [ticksStSignextend]; rw [hgas, Sat256.subNat_sub_add_of_sub_sub]
      · simp only [ticksStSignextend]; exact hmem
      · simp only [ticksStSignextend]; exact haw
      · simp only [ticksStSignextend]; exact hrdata
      · simp only [ticksStSignextend]; exact hacc
      · exact hee
      · exact hworld

private theorem uniswapV3PoolPatchPreservesJumpDest10605 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨10605⟩ 0 = true := by
  native_decide

private theorem uniswapV3PoolTicksRoutinePatchDisjoint {v : PoolImmutables}
    {pc : UInt256} (hlo : 10605 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
    ∀ p ∈ patches v, pc.toNat + 33 ≤ p.1 ∨ p.1 + 32 ≤ pc.toNat := by
  intro p hp
  simp [patches, patchesFrom, offsets, immValues, wordBytes?, valueToWord, List.lookup] at hp
  rcases hp with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl
  all_goals omega

theorem uniswapV3PoolJumpDestPatched10605 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨10605⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolPatchPreservesJumpDest10605

theorem uniswapV3PoolTicksReachEntry {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 24 == I.calldata.extract 0 4) = true) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2088⟩ [solcSelectorWord I]
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  obtain ⟨_, _, h32⟩ := uniswapV3PoolReachSelector32
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize
  have hword : solcSelectorWord I = uniswapV3PoolSelNat 24 := by
    simpa [uniswapV3PoolSelBytes, uniswapV3PoolSelNat] using
      solcSelectorWord_eq_of_beq I hsz 0xf3 0x0d 0xba 0x93
        (uniswapV3PoolSelNat 24) (by native_decide) hsel
  have hgt32 : UInt256.gt (armSelNat code ⟨32⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h43 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨43⟩) hpatch h32 hgt32
  have hgt43 : UInt256.gt (armSelNat code ⟨43⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h54 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨54⟩) hpatch h43 hgt43
  have hgt54 : UInt256.gt (armSelNat code ⟨54⟩) (solcSelectorWord I) = ⟨0⟩ := by
    rw [uniswapV3PoolArmSelNatPatchedEqTemplate2258 hpatch (by native_decide), hword]
    native_decide
  have h65 := uniswapV3PoolSelectorSplitNotTakenTo (next := ⟨65⟩) hpatch h54 hgt54
  have hmiss22 : (uniswapV3PoolSelBytes 22 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h76 := uniswapV3PoolSelectorArmMissToOf (i := 22) (next := ⟨76⟩)
    hpatch hsz hmiss22 h65
  have hmiss23 : (uniswapV3PoolSelBytes 23 == I.calldata.extract 0 4) = false :=
    uniswapV3PoolSelectorMissOfHit I (by native_decide) hsel
  have h87 := uniswapV3PoolSelectorArmMissToOf (i := 23) (next := ⟨87⟩)
    hpatch hsz hmiss23 h76
  have h2088 := uniswapV3PoolSelectorArmHitTo (i := 24) (target := ⟨2088⟩)
    hpatch hsz hsel h87
  exact ⟨_, _, h2088⟩

private theorem uniswapV3PoolTicksDecodedReachRoutine {v : PoolImmutables}
    {code : ByteArray} {ee : ExecutionEnv} {g : Sat256} {s0 : State}
    {de ret : UInt256} {R : List UInt256} {mem : ByteArray} {aw : UInt256}
    {rdata : ByteArray} {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2110⟩ (de :: ⟨4⟩ :: ret :: R) mem aw rdata acc k C)
    (hov : R.length + 3 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨10605⟩ (ticksArgCleanWord ee :: ret :: R)
      mem aw rdata acc k' C' := by
  have rd2111 : RD code ee g s0 ⟨2111⟩ (de :: ⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1) (C + 1) := by
    simpa using h.jumpdest
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd2112 : RD code ee g s0 ⟨2112⟩ (⟨4⟩ :: ret :: R)
      mem aw rdata acc (k + 1 + 1) (C + 1 + 2) := by
    simpa using rd2111.pop
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd2113 : RD code ee g s0 ⟨2113⟩ (ticksArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1) (C + 1 + 2 + 3) := by
    simpa [ticksArgWord, calldataWord, show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      using (rd2112.calldataload
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd2115 : RD code ee g s0 ⟨2115⟩ (⟨2⟩ :: ticksArgWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3) := by
    simpa using rd2113.push1 ⟨2⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  have rd2116 : RD code ee g s0 ⟨2116⟩ (ticksArgCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1) (C + 1 + 2 + 3 + 3 + 5) := by
    simpa [ticksArgCleanWord] using
      (ticksRDSignextend rd2115
        (by
          rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
          native_decide)
        (by evm_ov))
  have rd2119 : RD code ee g s0 ⟨2119⟩ (⟨10605⟩ :: ticksArgCleanWord ee :: ret :: R)
      mem aw rdata acc (k + 1 + 1 + 1 + 1 + 1 + 1)
        (C + 1 + 2 + 3 + 3 + 5 + 3) := by
    simpa using rd2116.push2 ⟨10605⟩
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide)
      (by evm_ov)
  exact ⟨_, _, rd2119.jump
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (uniswapV3PoolJumpDestPatched10605 hpatch)
    (by evm_ov)⟩

set_option maxHeartbeats 3000000 in
private theorem uniswapV3PoolTicksExternalLenOk {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hreach : ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2088⟩
      [solcSelectorWord I] solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C)
    (hsz36 : 36 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size) :
    ∃ k C, RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2110⟩
      (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩ :: ⟨4⟩ :: ⟨2120⟩ ::
        [solcSelectorWord I])
      solcFreePtrMem (UInt256.ofNat 3) ByteArray.empty (cA, σ) k C := by
  exact RD.solcExternalStaticArgsLenOk (need := ⟨32⟩)
    (entry := ⟨2088⟩) (ret := ⟨2120⟩) (decoded := ⟨2110⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (solcDecodeLenCheckOkUnsigned (by simpa using hsz36) hsize)

theorem uniswapV3PoolTicksEvmDecodeShort {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 24 == I.calldata.extract 0 4) = true)
    (hshort : I.calldata.size < 36) :
    RDrev code g (initState cA gh bl σ σ₀ g A I) := by
  have hreach := uniswapV3PoolTicksReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hlt :
      UInt256.lt (UInt256.sub (UInt256.ofNat I.calldata.size) ⟨4⟩) ⟨32⟩ = ⟨1⟩ := by
    apply ult_one
    rw [usub_ofNat_word_toNat (by
      rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
      omega) hsize]
    rw [show (⟨32⟩ : UInt256).toNat = 32 from by decide]
    rw [show (⟨4⟩ : UInt256).toNat = 4 from by decide]
    omega
  exact RD.solcExternalStaticArgsShortReverts (need := ⟨32⟩)
    (entry := ⟨2088⟩) (ret := ⟨2120⟩) (decoded := ⟨2110⟩) hreach
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    (by rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]; native_decide)
    hlt

set_option maxHeartbeats 3000000 in
private theorem uniswapV3PoolTicksRoutine {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ} {ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨10605⟩ (ticksArgCleanWord ee :: ret :: R)
      solcFreePtrMem (UInt256.ofNat 3) rdata (cA, σ) k C)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 12 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (ticksInitializedRawWord σ ee :: ticksSecondsOutsideWord σ ee ::
        ticksSecondsPerLiquidityWord σ ee :: ticksTickCumulativeReturnWord σ ee ::
        ticksFeeGrowthOutside1Word σ ee :: ticksFeeGrowthOutside0Word σ ee ::
        ticksLiquidityNetReturnWord σ ee :: ticksLiquidityGrossWord σ ee :: ret :: R)
      (solcMappingHashMem ⟨5⟩ (ticksArgCleanWord ee)) (UInt256.ofNat 3)
      rdata (cA, σ) k' C' := by
  have hdecode {pc : UInt256} (hlo : 10605 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 11259) :
      decode code pc = decode uniswapV3PoolBytecode pc := by
    rw [uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch (by
        have hsize : 11259 ≤ uniswapV3PoolBytecode.size := by native_decide
        omega)
      (uniswapV3PoolTicksRoutinePatchDisjoint hlo hhi)]
  have hd10605 : decode code ⟨10605⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10606 : decode code ⟨10606⟩ = some (.Push .PUSH1, some (⟨5⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10608 : decode code ⟨10608⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10610 : decode code ⟨10610⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10611 : decode code ⟨10611⟩ = some (.Push .PUSH1, some (⟨0⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10613 : decode code ⟨10613⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10614 : decode code ⟨10614⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10615 : decode code ⟨10615⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10616 : decode code ⟨10616⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10618 : decode code ⟨10618⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10619 : decode code ⟨10619⟩ = some (.KECCAK256, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10620 : decode code ⟨10620⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10621 : decode code ⟨10621⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10622 : decode code ⟨10622⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10624 : decode code ⟨10624⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10625 : decode code ⟨10625⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10626 : decode code ⟨10626⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10627 : decode code ⟨10627⟩ = some (.Push .PUSH1, some (⟨2⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10629 : decode code ⟨10629⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10630 : decode code ⟨10630⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10631 : decode code ⟨10631⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10632 : decode code ⟨10632⟩ = some (.Push .PUSH1, some (⟨3⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10634 : decode code ⟨10634⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10635 : decode code ⟨10635⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10636 : decode code ⟨10636⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10637 : decode code ⟨10637⟩ = some (.SLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10638 : decode code ⟨10638⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10640 : decode code ⟨10640⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10642 : decode code ⟨10642⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10644 : decode code ⟨10644⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10645 : decode code ⟨10645⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10646 : decode code ⟨10646⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10647 : decode code ⟨10647⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10648 : decode code ⟨10648⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10649 : decode code ⟨10649⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10651 : decode code ⟨10651⟩ = some (.Push .PUSH1, some (⟨128⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10653 : decode code ⟨10653⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10654 : decode code ⟨10654⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10655 : decode code ⟨10655⟩ = some (.SWAP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10656 : decode code ⟨10656⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10657 : decode code ⟨10657⟩ = some (.Push .PUSH1, some (⟨15⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10659 : decode code ⟨10659⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10660 : decode code ⟨10660⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10661 : decode code ⟨10661⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10662 : decode code ⟨10662⟩ = some (.Push .PUSH1, some (⟨6⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10664 : decode code ⟨10664⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10665 : decode code ⟨10665⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10666 : decode code ⟨10666⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10667 : decode code ⟨10667⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10668 : decode code ⟨10668⟩ =
      some (.Push .PUSH8, some (⟨72057594037927936⟩, 8)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10677 : decode code ⟨10677⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10678 : decode code ⟨10678⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10679 : decode code ⟨10679⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10681 : decode code ⟨10681⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10683 : decode code ⟨10683⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10685 : decode code ⟨10685⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10686 : decode code ⟨10686⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10687 : decode code ⟨10687⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10688 : decode code ⟨10688⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10689 : decode code ⟨10689⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10691 : decode code ⟨10691⟩ = some (.Push .PUSH1, some (⟨216⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10693 : decode code ⟨10693⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10694 : decode code ⟨10694⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10695 : decode code ⟨10695⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10696 : decode code ⟨10696⟩ =
      some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10701 : decode code ⟨10701⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10702 : decode code ⟨10702⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10703 : decode code ⟨10703⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10705 : decode code ⟨10705⟩ = some (.Push .PUSH1, some (⟨248⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10707 : decode code ⟨10707⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10708 : decode code ⟨10708⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10709 : decode code ⟨10709⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10710 : decode code ⟨10710⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10712 : decode code ⟨10712⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10713 : decode code ⟨10713⟩ = some (.DUP9, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd10714 : decode code ⟨10714⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have rd10619Pre := evm_run h with [
    raw jumpdest hd10605 (by evm_ov),
    raw push1 ⟨5⟩ hd10606 (by evm_ov),
    raw push1 ⟨32⟩ hd10608 (by evm_ov),
    raw mstore 0 (solcMappingBaseSlotMem ⟨5⟩) (UInt256.ofNat 3) hd10610 mem_cost
      (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨0⟩ hd10611 (by evm_ov),
    raw swap1 hd10613 (by evm_ov),
    raw dup2 hd10614 (by evm_ov),
    raw mstore 0 (solcMappingHashMem ⟨5⟩ (ticksArgCleanWord ee))
      (UInt256.ofNat 3) hd10615 mem_cost (by rfl) (by native_decide) (by evm_ov),
    raw push1 ⟨64⟩ hd10616 (by evm_ov),
    raw swap1 hd10618 (by evm_ov)]
  have hslot := solcMappingKeccakSlot ⟨5⟩ (ticksArgCleanWord ee)
  have rd10620 := rd10619Pre.keccak256 0 (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee))
    (UInt256.ofNat 3) hd10619 mem_cost
    (by simpa [show (⟨0⟩ : UInt256).toNat = 0 from by decide,
      show (⟨64⟩ : UInt256).toNat = 64 from by decide] using hslot)
    (by native_decide) (by evm_ov)
  have rd10621 := evm_run rd10620 with [raw dup1 hd10620 (by evm_ov)]
  obtain ⟨_, _, rd10622⟩ := rd10621.sload hd10621 (by evm_ov)
  have rd10626Pre := evm_run rd10622 with [
    raw push1 ⟨1⟩ hd10622 (by evm_ov),
    raw dup3 hd10624 (by evm_ov),
    raw add hd10625 (by evm_ov)]
  obtain ⟨_, _, rd10627⟩ := rd10626Pre.sload hd10626 (by evm_ov)
  have rd10631Pre := evm_run rd10627 with [
    raw push1 ⟨2⟩ hd10627 (by evm_ov),
    raw dup4 hd10629 (by evm_ov),
    raw add hd10630 (by evm_ov)]
  obtain ⟨_, _, rd10632⟩ := rd10631Pre.sload hd10631 (by evm_ov)
  have rd10637Pre := evm_run rd10632 with [
    raw push1 ⟨3⟩ hd10632 (by evm_ov),
    raw swap1 hd10634 (by evm_ov),
    raw swap4 hd10635 (by evm_ov),
    raw add hd10636 (by evm_ov)]
  obtain ⟨_, _, rd10638⟩ := rd10637Pre.sload hd10637 (by evm_ov)
  have rd10659Pre := evm_run rd10638 with [
    raw push1 ⟨1⟩ hd10638 (by evm_ov),
    raw push1 ⟨1⟩ hd10640 (by evm_ov),
    raw push1 ⟨128⟩ hd10642 (by evm_ov),
    raw shl hd10644 (by evm_ov),
    raw sub hd10645 (by evm_ov),
    raw dup4 hd10646 (by evm_ov),
    raw and hd10647 (by evm_ov),
    raw swap4 hd10648 (by evm_ov),
    raw push1 ⟨1⟩ hd10649 (by evm_ov),
    raw push1 ⟨128⟩ hd10651 (by evm_ov),
    raw shl hd10653 (by evm_ov),
    raw swap1 hd10654 (by evm_ov),
    raw swap4 hd10655 (by evm_ov),
    raw div hd10656 (by evm_ov),
    raw push1 ⟨15⟩ hd10657 (by evm_ov)]
  have rd10660 := ticksRDSignextend rd10659Pre hd10659 (by evm_ov)
  have rd10666Pre := evm_run rd10660 with [
    raw swap3 hd10660 (by evm_ov),
    raw swap1 hd10661 (by evm_ov),
    raw push1 ⟨6⟩ hd10662 (by evm_ov),
    raw dup2 hd10664 (by evm_ov),
    raw swap1 hd10665 (by evm_ov)]
  have rd10667 := ticksRDSignextend rd10666Pre hd10666 (by evm_ov)
  have rd10668 := evm_run rd10667 with [raw swap1 hd10667 (by evm_ov)]
  have rd10677Ex : ∃ k' C', RD code ee g s0 ⟨10677⟩
      (⟨72057594037927936⟩ ::
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨3⟩)
            ⟨0⟩)) ::
        UInt256.signextend ⟨6⟩
          (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨3⟩)
            ⟨0⟩)) ::
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨2⟩)
            ⟨0⟩)) ::
        (σ.find? ee.codeOwner |>.option ⟨0⟩
          (fun ac => ac.storage.findD (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨1⟩)
            ⟨0⟩)) ::
        UInt256.signextend ⟨15⟩
          (UInt256.div
            (σ.find? ee.codeOwner |>.option ⟨0⟩
              (fun ac => ac.storage.findD (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee)) ⟨0⟩))
            (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩)) ::
        UInt256.land
          (σ.find? ee.codeOwner |>.option ⟨0⟩
            (fun ac => ac.storage.findD (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee)) ⟨0⟩))
          (UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩) ::
        ret :: R)
      (solcMappingHashMem ⟨5⟩ (ticksArgCleanWord ee)) (UInt256.ofNat 3)
      rdata (cA, σ) k' C' := by
    exact ⟨_, _, by
      simpa using rd10668.pushConst ⟨72057594037927936⟩
        (width := 8) (op := .PUSH8)
        (by decide : Operation.POp.PUSH8 ≠ .PUSH0) hd10668 (by evm_ov)⟩
  obtain ⟨_, _, rd10677⟩ := rd10677Ex
  have rd10714Pre := evm_run rd10677 with [
    raw dup2 hd10677 (by evm_ov),
    raw div hd10678 (by evm_ov),
    raw push1 ⟨1⟩ hd10679 (by evm_ov),
    raw push1 ⟨1⟩ hd10681 (by evm_ov),
    raw push1 ⟨160⟩ hd10683 (by evm_ov),
    raw shl hd10685 (by evm_ov),
    raw sub hd10686 (by evm_ov),
    raw and hd10687 (by evm_ov),
    raw swap1 hd10688 (by evm_ov),
    raw push1 ⟨1⟩ hd10689 (by evm_ov),
    raw push1 ⟨216⟩ hd10691 (by evm_ov),
    raw shl hd10693 (by evm_ov),
    raw dup2 hd10694 (by evm_ov),
    raw div hd10695 (by evm_ov),
    raw push4 ⟨4294967295⟩ hd10696 (by evm_ov),
    raw and hd10701 (by evm_ov),
    raw swap1 hd10702 (by evm_ov),
    raw push1 ⟨1⟩ hd10703 (by evm_ov),
    raw push1 ⟨248⟩ hd10705 (by evm_ov),
    raw shl hd10707 (by evm_ov),
    raw swap1 hd10708 (by evm_ov),
    raw div hd10709 (by evm_ov),
    raw push1 ⟨255⟩ hd10710 (by evm_ov),
    raw and hd10712 (by evm_ov),
    raw dup9 hd10713 (by evm_ov)]
  have rdRet := rd10714Pre.jump hd10714 hret (by evm_ov)
  have hbase : ticksBaseSlot ee = solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) :=
    ticksBaseSlot_eq_solcMappingSlot ee
  have hmask128 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  have hshift128 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩ = ticksShiftBytes 16 := by
    native_decide
  have hshift56 : (⟨72057594037927936⟩ : UInt256) = ticksShiftBytes 7 := by
    native_decide
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask := by
    native_decide
  have hshift216 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨216⟩ = ticksShiftBytes 27 := by
    native_decide
  have hmask32 : (⟨4294967295⟩ : UInt256) = ticksUint32Mask := by
    native_decide
  have hshift248 : UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨248⟩ = ticksShiftBytes 31 := by
    native_decide
  have hmask8 : (⟨255⟩ : UInt256) = slot0Uint8Mask := by
    native_decide
  have hsecondsLiqComm :
      UInt256.land slot0Uint160Mask
          (UInt256.div (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨3⟩))
            (ticksShiftBytes 7)) =
        UInt256.land
          (UInt256.div (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨3⟩))
            (ticksShiftBytes 7))
          slot0Uint160Mask := by
    rw [u256_land_comm]
  have hsecondsOutComm :
      UInt256.land ticksUint32Mask
          (UInt256.div (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨3⟩))
            (ticksShiftBytes 27)) =
        UInt256.land
          (UInt256.div (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨3⟩))
            (ticksShiftBytes 27))
          ticksUint32Mask := by
    rw [u256_land_comm]
  have hinitComm :
      UInt256.land slot0Uint8Mask
          (UInt256.div (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨3⟩))
            (ticksShiftBytes 31)) =
        UInt256.land
          (UInt256.div (solcSlotWord σ ee (solcMappingSlot ⟨5⟩ (ticksArgCleanWord ee) + ⟨3⟩))
            (ticksShiftBytes 31))
          slot0Uint8Mask := by
    rw [u256_land_comm]
  exact ⟨_, _, by
    rw [hmask128, hshift128, hshift56, hmask160, hshift216, hmask32, hshift248,
      hmask8] at rdRet
    simpa [ticksInitializedRawWord, ticksSecondsOutsideWord, ticksSecondsPerLiquidityWord,
      ticksTickCumulativeReturnWord, ticksFeeGrowthOutside1Word, ticksFeeGrowthOutside0Word,
      ticksLiquidityNetReturnWord, ticksLiquidityNetRawWord, ticksLiquidityGrossWord,
      ticksPacked3Word, ticksPacked3Slot, ticksPacked0Word, solcSlotWord, hbase,
      hsecondsLiqComm, hsecondsOutComm, hinitComm] using rdRet⟩

set_option maxHeartbeats 3000000 in
theorem uniswapV3PoolTicksReturn {v : PoolImmutables} {code : ByteArray}
    {g : Sat256} {s0 : State} {ee : ExecutionEnv} {k C : ℕ}
    {initialized secondsOut secondsLiq tick fee1 fee0 net gross : UInt256}
    {R : List UInt256} {scratch rdata : ByteArray}
    {acc : Batteries.RBSet AccountAddress compare × AccountMap}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨2120⟩
      (initialized :: secondsOut :: secondsLiq :: tick :: fee1 :: fee0 :: net :: gross :: R)
      scratch (UInt256.ofNat 3) rdata acc k C)
    (hscratch : scratch.size = 96)
    (hread64 : scratch.readWithPadding 64 32 = UInt256.toByteArray ⟨128⟩)
    (hov : R.length + 24 ≤ 1024) :
    RDret code g s0 acc
      (UInt256.toByteArray (UInt256.land gross uint128Mask) ++
        UInt256.toByteArray (UInt256.signextend ⟨15⟩ net) ++
          UInt256.toByteArray fee0 ++ UInt256.toByteArray fee1 ++
            UInt256.toByteArray (UInt256.signextend ⟨6⟩ tick) ++
              UInt256.toByteArray (UInt256.land secondsLiq slot0Uint160Mask) ++
                UInt256.toByteArray (UInt256.land secondsOut ticksUint32Mask) ++
                  UInt256.toByteArray (slot0BoolReturnWord initialized)) := by
  let gross' := UInt256.land gross uint128Mask
  let net' := UInt256.signextend ⟨15⟩ net
  let tick' := UInt256.signextend ⟨6⟩ tick
  let secondsLiq' := UInt256.land secondsLiq slot0Uint160Mask
  let secondsOut' := UInt256.land secondsOut ticksUint32Mask
  let initialized' := slot0BoolReturnWord initialized
  have hmask128 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨128⟩) ⟨1⟩ = uint128Mask := by
    native_decide
  have hmask160 :
      UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
        slot0Uint160Mask := by
    native_decide
  have hmask32 : (⟨4294967295⟩ : UInt256) = ticksUint32Mask := by
    native_decide
  have rd2134 := evm_run h with [
    raw jumpdest (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨64⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 3) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost (ticksScratch_mload64 hscratch hread64) (by decide)
      (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨128⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov)]
  have rd2135 := RD.swap10 rd2134
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by omega)
  have rd2136 := evm_run rd2135 with [
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov)]
  have rd2137 := RD.dup10 rd2136
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by omega)
  have rd2140 := evm_run rd2137 with [
    raw mstore 6 (ticksScratchReturnMem1 scratch gross') (UInt256.ofNat 5) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        dsimp [gross']
        rw [hmask128, show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          ticksScratchReturnMem1_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨15⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov)]
  have rd2141 := RD.swap8 rd2140
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2142 := evm_run rd2141 with [
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov)]
  have rd2143 := RD.swap8 rd2142
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by simp only [List.length_cons]; omega)
  have rd2144 := ticksRDSignextend rd2143
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by evm_ov)
  have rd2146 := evm_run rd2144 with [
    raw push1 ⟨32⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov)]
  have rd2147 := RD.dup10 rd2146
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by omega)
  have rd2169 := evm_run rd2147 with [
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (ticksScratchReturnMem2 scratch gross' net') (UInt256.ofNat 6) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        dsimp [net']
        rw [show ((⟨128⟩ : UInt256) + ⟨32⟩).toNat = 160 from by decide,
          ticksScratchReturnMem2_eq]
        rfl)
      (by decide) (by evm_ov),
    raw dup8 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup8 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap6 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap6 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (ticksScratchReturnMem3 scratch gross' net' fee0) (UInt256.ofNat 7) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (by
        rw [show ((⟨64⟩ : UInt256) + ⟨128⟩).toNat = 192 from by decide,
          ticksScratchReturnMem3_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨96⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup8 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap4 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap4 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (ticksScratchReturnMem4 scratch gross' net' fee0 fee1)
      (UInt256.ofNat 8) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        rw [show ((⟨128⟩ : UInt256) + ⟨96⟩).toNat = 224 from by decide,
          ticksScratchReturnMem4_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨6⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov)]
  have rd2170 := ticksRDSignextend rd2169
    (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide)
    (by evm_ov)
  exact evm_run rd2170 with [
    raw push1 ⟨128⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup7 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3 (ticksScratchReturnMem5 scratch gross' net' fee0 fee1 tick')
      (UInt256.ofNat 9) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [tick']
        rw [show ((⟨128⟩ : UInt256) + ⟨128⟩).toNat = 256 from by decide,
          ticksScratchReturnMem5_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨1⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw shl (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨160⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup6 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3
      (ticksScratchReturnMem6 scratch gross' net' fee0 fee1 tick' secondsLiq')
      (UInt256.ofNat 10) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [secondsLiq']
        rw [hmask160, show ((⟨128⟩ : UInt256) + ⟨160⟩).toNat = 288 from by decide,
          u256_land_comm slot0Uint160Mask secondsLiq, ticksScratchReturnMem6_eq]
        rfl)
      (by decide) (by evm_ov),
    raw push4 ⟨4294967295⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw and (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨192⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup5 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3
      (ticksScratchReturnMem7 scratch gross' net' fee0 fee1 tick' secondsLiq' secondsOut')
      (UInt256.ofNat 11) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [secondsOut']
        rw [hmask32, show ((⟨128⟩ : UInt256) + ⟨192⟩).toNat = 320 from by decide,
          u256_land_comm ticksUint32Mask secondsOut, ticksScratchReturnMem7_eq]
        rfl)
      (by decide) (by evm_ov),
    raw iszero (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw iszero (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push1 ⟨224⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup4 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw mstore 3
      (ticksScratchReturnMem scratch gross' net' fee0 fee1 tick' secondsLiq' secondsOut'
        initialized')
      (UInt256.ofNat 12) (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [initialized', slot0BoolReturnWord]
        rw [show ((⟨128⟩ : UInt256) + ⟨224⟩).toNat = 352 from by decide,
          ticksScratchReturnMem_eq]
        rfl)
      (by decide) (by evm_ov),
    raw mload 0 ⟨128⟩ (UInt256.ofNat 12) (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) mem_cost
      (ticksScratchReturnMem_mload64 gross' net' fee0 fee1 tick' secondsLiq' secondsOut'
        initialized' hscratch hread64)
      (by decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw dup2 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw sub (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw push2 ⟨256⟩ (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw add (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw swap1 (by
      rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
      native_decide) (by evm_ov),
    raw ret 0
      (UInt256.toByteArray gross' ++ UInt256.toByteArray net' ++
        UInt256.toByteArray fee0 ++ UInt256.toByteArray fee1 ++
          UInt256.toByteArray tick' ++ UInt256.toByteArray secondsLiq' ++
            UInt256.toByteArray secondsOut' ++ UInt256.toByteArray initialized')
      (by
        rw [uniswapV3PoolDecodePatchedEqTemplate2258 hpatch (by native_decide)]
        native_decide) mem_cost
      (by
        dsimp [gross', net', tick', secondsLiq', secondsOut', initialized']
        rw [show (⟨128⟩ : UInt256).toNat = 128 from by decide,
          show ((⟨256⟩ : UInt256) + UInt256.sub (⟨128⟩ : UInt256) ⟨128⟩).toNat =
            256 from by decide]
        exact ticksScratchReturnMem_read128_256
          (UInt256.land gross uint128Mask) (UInt256.signextend ⟨15⟩ net) fee0 fee1
          (UInt256.signextend ⟨6⟩ tick) (UInt256.land secondsLiq slot0Uint160Mask)
          (UInt256.land secondsOut ticksUint32Mask) (slot0BoolReturnWord initialized)
          hscratch)
      (by evm_ov)]

private theorem uniswapV3PoolTicksLoadedToReturn {v : PoolImmutables}
    {code : ByteArray} {cA gh bl σ σ₀ A I} {g : Sat256} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (rdLoaded : RD code I g (initState cA gh bl σ σ₀ g A I) ⟨2120⟩
      (ticksInitializedRawWord σ I :: ticksSecondsOutsideWord σ I ::
        ticksSecondsPerLiquidityWord σ I :: ticksTickCumulativeReturnWord σ I ::
        ticksFeeGrowthOutside1Word σ I :: ticksFeeGrowthOutside0Word σ I ::
        ticksLiquidityNetReturnWord σ I :: ticksLiquidityGrossWord σ I ::
          ⟨2120⟩ :: [solcSelectorWord I])
      (solcMappingHashMem ⟨5⟩ (ticksArgCleanWord I)) (UInt256.ofNat 3)
      ByteArray.empty (cA, σ) k C) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (ticksLiquidityGrossWord σ I) uint128Mask) ++
        UInt256.toByteArray (UInt256.signextend ⟨15⟩ (ticksLiquidityNetReturnWord σ I)) ++
          UInt256.toByteArray (ticksFeeGrowthOutside0Word σ I) ++
            UInt256.toByteArray (ticksFeeGrowthOutside1Word σ I) ++
              UInt256.toByteArray
                (UInt256.signextend ⟨6⟩ (ticksTickCumulativeReturnWord σ I)) ++
                UInt256.toByteArray
                  (UInt256.land (ticksSecondsPerLiquidityWord σ I) slot0Uint160Mask) ++
                  UInt256.toByteArray
                    (UInt256.land (ticksSecondsOutsideWord σ I) ticksUint32Mask) ++
                    UInt256.toByteArray
                      (slot0BoolReturnWord (ticksInitializedRawWord σ I))) := by
  exact uniswapV3PoolTicksReturn hpatch
    (initialized := ticksInitializedRawWord σ I)
    (secondsOut := ticksSecondsOutsideWord σ I)
    (secondsLiq := ticksSecondsPerLiquidityWord σ I)
    (tick := ticksTickCumulativeReturnWord σ I)
    (fee1 := ticksFeeGrowthOutside1Word σ I)
    (fee0 := ticksFeeGrowthOutside0Word σ I)
    (net := ticksLiquidityNetReturnWord σ I)
    (gross := ticksLiquidityGrossWord σ I)
    (R := [⟨2120⟩, solcSelectorWord I]) rdLoaded
    (solcMappingHashMem_size ⟨5⟩ (ticksArgCleanWord I))
    (solcMappingHashMem_read64 ⟨5⟩ (ticksArgCleanWord I))
    (by simp only [List.length_cons, List.length_nil]; omega)

theorem uniswapV3PoolTicksEvm {v : PoolImmutables} {code : ByteArray}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (hsel : (uniswapV3PoolSelBytes 24 == I.calldata.extract 0 4) = true)
    (hsz36 : 36 ≤ I.calldata.size) :
    RDret code g (initState cA gh bl σ σ₀ g A I) (cA, σ)
      (UInt256.toByteArray (UInt256.land (ticksLiquidityGrossWord σ I) uint128Mask) ++
        UInt256.toByteArray (UInt256.signextend ⟨15⟩ (ticksLiquidityNetReturnWord σ I)) ++
          UInt256.toByteArray (ticksFeeGrowthOutside0Word σ I) ++
            UInt256.toByteArray (ticksFeeGrowthOutside1Word σ I) ++
              UInt256.toByteArray
                (UInt256.signextend ⟨6⟩ (ticksTickCumulativeReturnWord σ I)) ++
                UInt256.toByteArray
                  (UInt256.land (ticksSecondsPerLiquidityWord σ I) slot0Uint160Mask) ++
                  UInt256.toByteArray
                    (UInt256.land (ticksSecondsOutsideWord σ I) ticksUint32Mask) ++
                    UInt256.toByteArray
                      (slot0BoolReturnWord (ticksInitializedRawWord σ I))) := by
  have hreach := uniswapV3PoolTicksReachEntry
    (v := v) (code := code) (cA := cA) (gh := gh) (bl := bl) (σ := σ)
    (σ₀ := σ₀) (A := A) (I := I) (g := g) hpatch hcode hwv hsz hsize hsel
  have hdecoded := uniswapV3PoolTicksExternalLenOk hpatch hreach hsz36 hsize
  obtain ⟨_, _, rdDecoded⟩ := hdecoded
  obtain ⟨_, _, rdRoutine⟩ := uniswapV3PoolTicksDecodedReachRoutine hpatch rdDecoded
    (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨_, _, rdLoaded⟩ := uniswapV3PoolTicksRoutine hpatch rdRoutine
    (uniswapV3PoolJumpDestPatched2258 hpatch (by native_decide))
    (by simp only [List.length_cons, List.length_nil]; omega)
  exact uniswapV3PoolTicksLoadedToReturn hpatch rdLoaded

theorem ticksReturnEncoding (σ : AccountMap) (I : ExecutionEnv) :
    encodeReturnValues? [uint128, int128, uint256, uint256, int56, uint160, uint32, boolTy]
        (ticksReturnValues σ I) =
      some (UInt256.toByteArray (UInt256.land (ticksLiquidityGrossWord σ I) uint128Mask) ++
        UInt256.toByteArray (UInt256.signextend ⟨15⟩ (ticksLiquidityNetReturnWord σ I)) ++
          UInt256.toByteArray (ticksFeeGrowthOutside0Word σ I) ++
            UInt256.toByteArray (ticksFeeGrowthOutside1Word σ I) ++
              UInt256.toByteArray
                (UInt256.signextend ⟨6⟩ (ticksTickCumulativeReturnWord σ I)) ++
                UInt256.toByteArray
                  (UInt256.land (ticksSecondsPerLiquidityWord σ I) slot0Uint160Mask) ++
                  UInt256.toByteArray
                    (UInt256.land (ticksSecondsOutsideWord σ I) ticksUint32Mask) ++
                    UInt256.toByteArray
                      (slot0BoolReturnWord (ticksInitializedRawWord σ I))) := by
  have hgross : UInt256.land (ticksLiquidityGrossWord σ I) uint128Mask =
      ticksLiquidityGrossWord σ I := by
    exact uint128Mask_clean (by
      simpa [ticksLiquidityGrossWord] using uint128Mask_bound (ticksPacked0Word σ I))
  have hnet : UInt256.signextend ⟨15⟩ (ticksLiquidityNetReturnWord σ I) =
      ticksLiquidityNetReturnWord σ I := by
    dsimp [ticksLiquidityNetReturnWord]
    exact ticksSignextendFifteen_idempotent (ticksLiquidityNetRawWord σ I)
  have htick : UInt256.signextend ⟨6⟩ (ticksTickCumulativeReturnWord σ I) =
      ticksTickCumulativeReturnWord σ I := by
    dsimp [ticksTickCumulativeReturnWord]
    exact observationsSignextendSix_idempotent (ticksPacked3Word σ I)
  have hsecondsLiq :
      UInt256.land (ticksSecondsPerLiquidityWord σ I) slot0Uint160Mask =
        ticksSecondsPerLiquidityWord σ I := by
    exact slot0Uint160Mask_clean (by
      simpa [ticksSecondsPerLiquidityWord] using
        slot0Uint160Mask_bound
          (UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 7)))
  have hsecondsOut :
      UInt256.land (ticksSecondsOutsideWord σ I) ticksUint32Mask =
        ticksSecondsOutsideWord σ I := by
    exact ticksUint32Mask_clean (by
      simpa [ticksSecondsOutsideWord] using
        ticksUint32Mask_bound
          (UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 27)))
  rw [hgross, hnet, htick, hsecondsLiq, hsecondsOut]
  have hwordGross : EVM.word (ticksLiquidityGrossWord σ I).toNat =
      ticksLiquidityGrossWord σ I := u256_ofNat_toNat _
  have hwordFee0 : EVM.word (ticksFeeGrowthOutside0Word σ I).toNat =
      ticksFeeGrowthOutside0Word σ I := u256_ofNat_toNat _
  have hwordFee1 : EVM.word (ticksFeeGrowthOutside1Word σ I).toNat =
      ticksFeeGrowthOutside1Word σ I := u256_ofNat_toNat _
  have hwordSecondsLiq : EVM.word (ticksSecondsPerLiquidityWord σ I).toNat =
      ticksSecondsPerLiquidityWord σ I := u256_ofNat_toNat _
  have hwordSecondsOut : EVM.word (ticksSecondsOutsideWord σ I).toNat =
      ticksSecondsOutsideWord σ I := u256_ofNat_toNat _
  have hgrossLt : (ticksLiquidityGrossWord σ I).toNat < EVM.twoPow 128 := by
    simpa [ticksLiquidityGrossWord] using uint128Mask_bound (ticksPacked0Word σ I)
  have hfee0Lt : (ticksFeeGrowthOutside0Word σ I).toNat < EVM.twoPow 256 := by
    change (ticksFeeGrowthOutside0Word σ I).val.val < EVM.twoPow 256
    exact (ticksFeeGrowthOutside0Word σ I).val.isLt
  have hfee1Lt : (ticksFeeGrowthOutside1Word σ I).toNat < EVM.twoPow 256 := by
    change (ticksFeeGrowthOutside1Word σ I).val.val < EVM.twoPow 256
    exact (ticksFeeGrowthOutside1Word σ I).val.isLt
  have hsecondsLiqLt : (ticksSecondsPerLiquidityWord σ I).toNat < EVM.twoPow 160 := by
    simpa [ticksSecondsPerLiquidityWord] using
      slot0Uint160Mask_bound
        (UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 7))
  have hsecondsOutLt : (ticksSecondsOutsideWord σ I).toNat < EVM.twoPow 32 := by
    simpa [ticksSecondsOutsideWord] using
      ticksUint32Mask_bound
        (UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 27))
  have hencGross :
      encodeABIValue? uint128 (.int (Int.ofNat (ticksLiquidityGrossWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (ticksLiquidityGrossWord σ I)) := by
    simp [uint128, uint128Int, encodeABIValue?, encodeABIWord?, hwordGross, hgrossLt]
  have hencNet :
      encodeABIValue? int128
          (wordToElem (.int int128Int) (ticksLiquidityNetStorageWord σ I)) =
        some (EVM.Word.toBytesBE (ticksLiquidityNetReturnWord σ I)) := by
    change encodeABIValue? int128
        (.int (ticksSint128Value (ticksLiquidityNetStorageWord σ I))) =
      some (EVM.Word.toBytesBE (ticksLiquidityNetReturnWord σ I))
    have hge := ticksSint128Value_ge (ticksLiquidityNetStorageWord σ I)
    have hlt := ticksSint128Value_lt (ticksLiquidityNetStorageWord σ I)
    have hword : EVM.wordOfInt
          (ticksSint128Value (ticksLiquidityNetStorageWord σ I)) =
        ticksLiquidityNetReturnWord σ I := by
      dsimp [ticksLiquidityNetStorageWord, ticksLiquidityNetReturnWord]
      exact ticksLiquidityNetRawValue_wordOfInt (ticksLiquidityNetRawWord σ I)
    simp only [int128, int128Int, encodeABIValue?, encodeABIWord?]
    rw [if_neg (by decide : 128 ≠ 0), if_pos]
    · rw [hword]
      rfl
    · constructor
      · simpa [EVM.twoPow] using hge
      · simpa [EVM.twoPow] using hlt
  have hencFee0 :
      encodeABIValue? uint256 (.int (Int.ofNat (ticksFeeGrowthOutside0Word σ I).toNat)) =
        some (EVM.Word.toBytesBE (ticksFeeGrowthOutside0Word σ I)) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hwordFee0, hfee0Lt]
  have hencFee1 :
      encodeABIValue? uint256 (.int (Int.ofNat (ticksFeeGrowthOutside1Word σ I).toNat)) =
        some (EVM.Word.toBytesBE (ticksFeeGrowthOutside1Word σ I)) := by
    simp [uint256, uint256Int, encodeABIValue?, encodeABIWord?, hwordFee1, hfee1Lt]
  have hencTick :
      encodeABIValue? int56
          (wordToElem (.int int56Int) (ticksTickCumulativeStorageWord σ I)) =
        some (EVM.Word.toBytesBE (ticksTickCumulativeReturnWord σ I)) := by
    change encodeABIValue? int56
        (.int (observationsSint56Value (ticksTickCumulativeStorageWord σ I))) =
      some (EVM.Word.toBytesBE (ticksTickCumulativeReturnWord σ I))
    have hge := observationsSint56Value_ge (ticksTickCumulativeStorageWord σ I)
    have hlt := observationsSint56Value_lt (ticksTickCumulativeStorageWord σ I)
    have hdiv0 :
        UInt256.div (ticksPacked3Word σ I) (ticksShiftBytes 0) =
          ticksPacked3Word σ I := by
      apply u256_inj
      rw [udiv_toNat]
      simp only [ticksShiftBytes, Nat.pow_zero]
      rw [show (UInt256.ofNat 1).toNat = 1 by decide]
      exact Nat.div_one (ticksPacked3Word σ I).toNat
    have hword : EVM.wordOfInt
          (observationsSint56Value (ticksTickCumulativeStorageWord σ I)) =
        ticksTickCumulativeReturnWord σ I := by
      dsimp [ticksTickCumulativeStorageWord, ticksTickCumulativeRawWord,
        ticksTickCumulativeReturnWord]
      rw [hdiv0]
      exact observationsTickRawValue_wordOfInt (ticksPacked3Word σ I)
    simp only [int56, int56Int, encodeABIValue?, encodeABIWord?]
    rw [if_neg (by decide : 56 ≠ 0), if_pos]
    · rw [hword]
      rfl
    · constructor
      · simpa [EVM.twoPow] using hge
      · simpa [EVM.twoPow] using hlt
  have hencSecondsLiq :
      encodeABIValue? uint160 (.int (Int.ofNat (ticksSecondsPerLiquidityWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (ticksSecondsPerLiquidityWord σ I)) := by
    simp [uint160, uint160Int, encodeABIValue?, encodeABIWord?, hwordSecondsLiq,
      hsecondsLiqLt]
  have hencSecondsOut :
      encodeABIValue? uint32 (.int (Int.ofNat (ticksSecondsOutsideWord σ I).toNat)) =
        some (EVM.Word.toBytesBE (ticksSecondsOutsideWord σ I)) := by
    simp [uint32, uint32Int, encodeABIValue?, encodeABIWord?, hwordSecondsOut,
      hsecondsOutLt]
  have hencInitialized :
      encodeABIValue? boolTy (wordToElem .bool (ticksInitializedRawWord σ I)) =
        some (EVM.Word.toBytesBE
          (slot0BoolReturnWord (ticksInitializedRawWord σ I))) :=
    slot0BoolABIEncoding (ticksInitializedRawWord σ I)
  have hhead :
      abiTupleHeadSize? [uint128, int128, uint256, uint256, int56, uint160, uint32,
        boolTy] = some 256 := by native_decide
  have hdyn128 : isDynamicABIType uint128 = false := by native_decide
  have hdynInt128 : isDynamicABIType int128 = false := by native_decide
  have hdyn256 : isDynamicABIType uint256 = false := by native_decide
  have hdyn56 : isDynamicABIType int56 = false := by native_decide
  have hdyn160 : isDynamicABIType uint160 = false := by native_decide
  have hdyn32 : isDynamicABIType uint32 = false := by native_decide
  have hdynBool : isDynamicABIType boolTy = false := by native_decide
  rw [toByteArray_eq_toBytesBE (ticksLiquidityGrossWord σ I),
    toByteArray_eq_toBytesBE (ticksLiquidityNetReturnWord σ I),
    toByteArray_eq_toBytesBE (ticksFeeGrowthOutside0Word σ I),
    toByteArray_eq_toBytesBE (ticksFeeGrowthOutside1Word σ I),
    toByteArray_eq_toBytesBE (ticksTickCumulativeReturnWord σ I),
    toByteArray_eq_toBytesBE (ticksSecondsPerLiquidityWord σ I),
    toByteArray_eq_toBytesBE (ticksSecondsOutsideWord σ I),
    toByteArray_eq_toBytesBE (slot0BoolReturnWord (ticksInitializedRawWord σ I))]
  simp only [ticksReturnValues, encodeReturnValues?, encodeABIValues?,
    encodeABIValuesFrom?, hhead, hencGross, hencNet, hencFee0, hencFee1, hencTick,
    hencSecondsLiq, hencSecondsOut, hencInitialized, hdyn128, hdynInt128, hdyn256,
    hdyn56, hdyn160, hdyn32, hdynBool, bind, Option.bind, Bool.false_eq_true, if_false,
    List.nil_append, List.append_nil]
  apply congrArg some
  apply ByteArray.ext
  apply Array.toList_inj.mp
  simp

theorem uniswapV3PoolTicksBodyCore {v : PoolImmutables}
    {cA gh bl σ_evm σ_solm σ₀ A I} {g : UInt256} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hcode : I.code = code) (hwv : I.weiValue = ⟨0⟩)
    (hsz : 4 ≤ I.calldata.size) (hsize : I.calldata.size < UInt256.size)
    (_hperm : I.perm = true)
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hsel : (uniswapV3PoolSelBytes 24 == I.calldata.extract 0 4) = true) :
    runtimeEquivalenceFor (config v) (contract v) cA gh bl σ_evm σ_solm σ₀ g A I := by
  have hdispatch := uniswapV3PoolDispatch_ticks (v := v) (cd := I.calldata) hsel
  have hvalue := uniswapV3PoolTicksValueTransport (σ_evm := σ_evm)
    (σ_solm := σ_solm) (I := I) hAccounts
  by_cases hsz36 : 36 ≤ I.calldata.size
  · have hdecode := uniswapV3PoolTicksDecodeOk (v := v) (I := I) hsz36
    have hbody := uniswapV3PoolTicksSourceBody (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ_solm) (σ₀ := σ₀) (A := A) (I := I)
      (g := Sat256.ofUInt256 g) hwv
    have hrd := uniswapV3PoolTicksEvm (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hsz36
    exact hrd.reEquivExecutionTransport hcode hdispatch hdecode hbody hvalue hAccounts
      (by
        rw [show ticksTransition.returnType =
          [uint128, int128, uint256, uint256, int56, uint160, uint32, boolTy] from rfl]
        exact returnEquiv.returned rfl (ticksReturnEncoding σ_evm I))
  · have hshort : I.calldata.size < 36 := by omega
    have hdecode := uniswapV3PoolTicksDecodeShort (v := v) (I := I) hshort
    have hrd := uniswapV3PoolTicksEvmDecodeShort (v := v) (code := code)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ_evm) (σ₀ := σ₀) (A := A)
      (I := I) (g := Sat256.ofUInt256 g) hpatch hcode hwv hsz hsize hsel hshort
    exact hrd.reEquivDecodingFailed hcode hdispatch hdecode

end Benchmarks.UniswapV3Pool
