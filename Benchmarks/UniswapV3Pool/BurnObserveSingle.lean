import Benchmarks.UniswapV3Pool.Observations
import Benchmarks.UniswapV3Pool.BurnNonzeroDeltaStart

open Solm ABI Ethereum Ethereum.EVM Benchmarks.UniswapV3Pool.Immutables
open Reasoning.Theory Reasoning.Reach Reasoning.Refinement

namespace Benchmarks.UniswapV3Pool

private theorem burnObserveSingleSolcSlotWord_eq_of_accountMapEquiv {σ τ : AccountMap}
    (h : accountMapEquiv σ τ) (I : ExecutionEnv) (slot : UInt256) :
    solcSlotWord σ I slot = solcSlotWord τ I slot := by
  have hslot := accountMapEquiv_storage_findD h I.codeOwner slot (⟨0⟩ : UInt256)
  simpa [solcSlotWord] using hslot

abbrev burnObserveSingleObservationKey (σ : AccountMap) (I : ExecutionEnv) : KeyValue :=
  .int (Int.ofNat (slot0ObservationIndexWord σ I).toNat)

abbrev burnObserveSingleObservationBaseSlot (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  observationBase (burnObserveSingleObservationKey σ I)

theorem burnObserveSingleObservationBaseSlot_eq (σ : AccountMap) (I : ExecutionEnv) :
    burnObserveSingleObservationBaseSlot σ I =
      ⟨8⟩ + slot0ObservationIndexWord σ I := by
  unfold burnObserveSingleObservationBaseSlot burnObserveSingleObservationKey observationBase
  rw [keyValueToWord_uint256]
  rw [u256_ofNat_toNat]

theorem burnObserveSingleObservationIndexWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    slot0ObservationIndexWord σ_evm I = slot0ObservationIndexWord σ_solm I := by
  unfold slot0ObservationIndexWord slot0SlotWord
  rw [burnObserveSingleSolcSlotWord_eq_of_accountMapEquiv hAccounts I ⟨0⟩]

theorem burnObserveSingleObservationBaseSlot_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnObserveSingleObservationBaseSlot σ_evm I =
      burnObserveSingleObservationBaseSlot σ_solm I := by
  rw [burnObserveSingleObservationBaseSlot_eq, burnObserveSingleObservationBaseSlot_eq,
    burnObserveSingleObservationIndexWord_transport hAccounts]

abbrev burnObserveSingleSlotWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  solcSlotWord σ I (burnObserveSingleObservationBaseSlot σ I)

theorem burnObserveSingleSlotWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnObserveSingleSlotWord σ_evm I = burnObserveSingleSlotWord σ_solm I := by
  unfold burnObserveSingleSlotWord
  rw [burnObserveSingleObservationBaseSlot_transport hAccounts]
  rw [burnObserveSingleSolcSlotWord_eq_of_accountMapEquiv hAccounts I
    (burnObserveSingleObservationBaseSlot σ_solm I)]

theorem burnObserveSingleMaskedSlotWord_eq (σ : AccountMap) (I : ExecutionEnv)
    (hidxLt16 : (slot0ObservationIndexWord σ I).toNat < EVM.twoPow 16) :
    solcSlotWord σ I (⟨8⟩ + ((⟨65535⟩ : UInt256).land
      (slot0ObservationIndexWord σ I))) =
        burnObserveSingleSlotWord σ I := by
  have hmask :
      UInt256.land (⟨65535⟩ : UInt256) (slot0ObservationIndexWord σ I) =
        slot0ObservationIndexWord σ I := by
    rw [show (⟨65535⟩ : UInt256) = slot0Uint16Mask by native_decide]
    exact slot0Uint16Mask_clean_left hidxLt16
  simp [burnObserveSingleSlotWord, burnObserveSingleObservationBaseSlot_eq, hmask]

abbrev burnObserveSingleLoadedObsWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  solcSlotWord σ I (⟨8⟩ + ((⟨65535⟩ : UInt256).land
    ((⟨65535⟩ : UInt256).land
      ((solcSlotWord σ I ⟨0⟩).div ((⟨1⟩ : UInt256).shiftLeft ⟨184⟩)))))

theorem burnObserveSingleLoadedObsWord_eq (σ : AccountMap) (I : ExecutionEnv)
    (hidxLt16 : (slot0ObservationIndexWord σ I).toNat < EVM.twoPow 16) :
    burnObserveSingleLoadedObsWord σ I = burnObserveSingleSlotWord σ I := by
  unfold burnObserveSingleLoadedObsWord
  rw [show ((⟨1⟩ : UInt256).shiftLeft ⟨184⟩) = slot0ShiftBytes 23 by
    native_decide]
  rw [show (⟨65535⟩ : UInt256).land
      ((solcSlotWord σ I ⟨0⟩).div (slot0ShiftBytes 23)) =
      slot0ObservationIndexWord σ I by
    rw [show (⟨65535⟩ : UInt256) = slot0Uint16Mask by native_decide]
    simp [slot0ObservationIndexWord, slot0SlotWord, u256_land_comm]]
  have hmask :
      UInt256.land (⟨65535⟩ : UInt256) (slot0ObservationIndexWord σ I) =
        slot0ObservationIndexWord σ I := by
    rw [show (⟨65535⟩ : UInt256) = slot0Uint16Mask by native_decide]
    exact slot0Uint16Mask_clean_left hidxLt16
  simpa [hmask] using burnObserveSingleMaskedSlotWord_eq σ I hidxLt16

abbrev burnObserveSingleBlockTimestampWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (burnObserveSingleSlotWord σ I) observationsUint32Mask

theorem burnObserveSingleBlockTimestampWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnObserveSingleBlockTimestampWord σ_evm I =
      burnObserveSingleBlockTimestampWord σ_solm I := by
  unfold burnObserveSingleBlockTimestampWord
  rw [burnObserveSingleSlotWord_transport hAccounts]

abbrev burnObserveSingleTickRawWord (σ : AccountMap) (I : ExecutionEnv) : UInt256 :=
  UInt256.div (burnObserveSingleSlotWord σ I) (observationsShiftBytes 4)

theorem burnObserveSingleTickRawWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnObserveSingleTickRawWord σ_evm I = burnObserveSingleTickRawWord σ_solm I := by
  unfold burnObserveSingleTickRawWord
  rw [burnObserveSingleSlotWord_transport hAccounts]

abbrev burnObserveSingleTickStorageWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.land (burnObserveSingleTickRawWord σ I) observationsUint56Mask

theorem burnObserveSingleTickStorageWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnObserveSingleTickStorageWord σ_evm I =
      burnObserveSingleTickStorageWord σ_solm I := by
  unfold burnObserveSingleTickStorageWord
  rw [burnObserveSingleTickRawWord_transport hAccounts]

abbrev burnObserveSingleTickReturnWord (σ : AccountMap) (I : ExecutionEnv) :
    UInt256 :=
  UInt256.signextend ⟨6⟩ (burnObserveSingleTickRawWord σ I)

theorem burnObserveSingleTickReturnWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnObserveSingleTickReturnWord σ_evm I =
      burnObserveSingleTickReturnWord σ_solm I := by
  unfold burnObserveSingleTickReturnWord
  rw [burnObserveSingleTickRawWord_transport hAccounts]

abbrev burnObserveSingleSecondsPerLiquidityWord (σ : AccountMap)
    (I : ExecutionEnv) : UInt256 :=
  UInt256.land (UInt256.div (burnObserveSingleSlotWord σ I) (observationsShiftBytes 11))
    slot0Uint160Mask

theorem burnObserveSingleSecondsPerLiquidityWord_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnObserveSingleSecondsPerLiquidityWord σ_evm I =
      burnObserveSingleSecondsPerLiquidityWord σ_solm I := by
  unfold burnObserveSingleSecondsPerLiquidityWord
  rw [burnObserveSingleSlotWord_transport hAccounts]

def burnObserveSingleLastEvaledRef (σ : AccountMap) (I : ExecutionEnv) :
    EvaledStorageRef :=
  { base := "observations", steps := [.aindex (burnObserveSingleObservationKey σ I)] }

def burnObserveSingleLastFieldEvaledRef (σ : AccountMap) (I : ExecutionEnv)
    (field : Ident) : EvaledStorageRef :=
  { base := "observations",
    steps := [.aindex (burnObserveSingleObservationKey σ I), .field field] }

abbrev burnObserveSingleAfterLastFrame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnObserveSingleStore σ I).insert "last"
      (.storageRef (burnObserveSingleLastEvaledRef σ I) observationStructTy) }

private theorem burnObserveSingleStorageTypeAtBase :
    storageTypeAt? storageDecls { base := "observations", steps := [] } =
      some (.array observationStructTy 65535) := by
  rfl

theorem burnObserveSingleArrayIndexInBounds_ok {v : PoolImmutables} (evm : EVM.State)
    (σ : AccountMap) (I : ExecutionEnv)
    (hbound : (slot0ObservationIndexWord σ I).toNat < 65535) :
    arrayIndexInBounds? (config v) evm (contract v).storage "observations" []
      (burnObserveSingleObservationKey σ I) = .ok () := by
  unfold arrayIndexInBounds?
  rw [show (contract v).storage = storageDecls by rfl, burnObserveSingleStorageTypeAtBase]
  change (if 0 ≤ Int.ofNat (slot0ObservationIndexWord σ I).toNat ∧
      Int.ofNat (slot0ObservationIndexWord σ I).toNat < (↑(65535 : Nat) : Int) then
        EvalResult.ok () else EvalResult.revert) = EvalResult.ok ()
  have hin : 0 ≤ Int.ofNat (slot0ObservationIndexWord σ I).toNat ∧
      Int.ofNat (slot0ObservationIndexWord σ I).toNat < (↑(65535 : Nat) : Int) := by
    constructor
    · exact Int.natCast_nonneg _
    · change ((slot0ObservationIndexWord σ I).toNat : Int) < (65535 : Int)
      exact_mod_cast hbound
  rw [if_pos hin]

theorem burnObserveSingleAfterLast_last (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnObserveSingleAfterLastFrame v σ I).locals.get? "last" =
      some (.storageRef (burnObserveSingleLastEvaledRef σ I) observationStructTy) := by
  rw [burnObserveSingleAfterLastFrame]
  exact store_get_self (burnObserveSingleStore σ I) "last"
    (.storageRef (burnObserveSingleLastEvaledRef σ I) observationStructTy)

theorem burnObserveSingleStore_time (σ : AccountMap) (I : ExecutionEnv) :
    (burnObserveSingleStore σ I).get? "time" = some (burnBlockTimestamp32Value I) := by
  rw [burnObserveSingleStore]
  exact store_get_self
    ((((((∅ : Store).insert "cardinality" (burnSlot0ObservationCardinalityValue σ I))
      |>.insert "liquidity" (burnPoolLiquidityValue σ I))
      |>.insert "index" (burnSlot0ObservationIndexValue σ I))
      |>.insert "tick" (burnSlot0TickValue σ I))
      |>.insert "secondsAgo" (.int 0))
    "time" (burnBlockTimestamp32Value I)

theorem burnObserveSingleAfterLast_time (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) :
    (burnObserveSingleAfterLastFrame v σ I).locals.get? "time" =
      some (burnBlockTimestamp32Value I) := by
  rw [burnObserveSingleAfterLastFrame]
  rw [store_get_ne (burnObserveSingleStore σ I) (k := "last") (a := "time")
    (.storageRef (burnObserveSingleLastEvaledRef σ I) observationStructTy)
    (by native_decide)]
  exact burnObserveSingleStore_time σ I

theorem burnObserveSingleEvalTimeAfterLast {v : PoolImmutables}
    {evm σ I} :
    evalExpr? (config v) (burnObserveSingleAfterLastFrame v σ I) evm
      (.var "time") = .ok (burnBlockTimestamp32Value I) := by
  simp only [evalExpr?, EvalResult.ofOption]
  rw [burnObserveSingleAfterLast_time (v := v) (σ := σ) (I := I)]

theorem burnObservationStorageLocLoad_blockTimestamp (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc base ⟨0, by decide⟩ ⟨4, by decide⟩
          (by decide) (.int uint32Int)) =
      .int (Int.ofNat (UInt256.land
        (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base)
        observationsUint32Mask).toNat) := by
  rw [← show UInt256.ofNat (2 ^ (8 * 4) - 1) = observationsUint32Mask by native_decide]
  simpa [loc, uint32Int] using
    storageLocLoad_uint_offset0 evm base (4 : Fin 33) ⟨32, by decide⟩
      (hbound := by decide) (by decide)

theorem burnObserveSingleEvalLastBlockTimestamp {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnObserveSingleAfterLastFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "last") "blockTimestamp") =
        .ok (.int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat)) := by
  rw [evalExpr?]
  have hlast :
      evalExpr? (config v) (burnObserveSingleAfterLastFrame v σ I)
          (initState cA gh bl σ σ₀ g A I) (.var "last") =
        .ok (.storageRef (burnObserveSingleLastEvaledRef σ I) observationStructTy) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [burnObserveSingleAfterLast_last (v := v) (σ := σ) (I := I)]
  rw [hlast]
  simp only [EvalResult.ofOption, EvalResult.bind, bind]
  change readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnObserveSingleLastFieldEvaledRef σ I "blockTimestamp")
      (.elem (.int uint32Int)) =
    .ok (.int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat))
  rw [readStorage?]
  simp only [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
    burnObserveSingleLastFieldEvaledRef, burnObserveSingleObservationKey]
  simpa [initState, burnObserveSingleBlockTimestampWord, burnObserveSingleSlotWord,
    solcSlotWord]
    using burnObservationStorageLocLoad_blockTimestamp (initState cA gh bl σ σ₀ g A I)
      (burnObserveSingleObservationBaseSlot σ I)

theorem burnObserveSingleEvalLastTimestampNeTimeFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsame :
      .int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat) =
        burnBlockTimestamp32Value I) :
    evalExpr? (config v) (burnObserveSingleAfterLastFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (neE (.field (.var "last") "blockTimestamp") (.var "time")) =
        .ok (.bool false) := by
  unfold neE
  rw [evalExpr?] <;> try decide
  rw [burnObserveSingleEvalLastBlockTimestamp (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)]
  rw [burnObserveSingleEvalTimeAfterLast (v := v)
    (evm := initState cA gh bl σ σ₀ g A I) (σ := σ) (I := I)]
  rw [hsame]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnBlockTimestamp32Value]

theorem burnObservationStorageLocLoad_tickCumulative (evm : EVM.State) (base : UInt256) :
    storageLocLoad evm
        (loc base ⟨4, by decide⟩ ⟨7, by decide⟩
          (by decide) (.int int56Int)) =
      wordToElem (.int int56Int)
        (UInt256.land
          (UInt256.div
            (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base)
            (observationsShiftBytes 4))
          observationsUint56Mask) := by
  rw [← show UInt256.ofNat (256 ^ (4 : Nat)) = observationsShiftBytes 4 by rfl]
  rw [← show UInt256.ofNat (256 ^ (7 : Nat) - 1) = observationsUint56Mask by
    native_decide]
  simpa [loc, int56Int] using
    storageLocLoad_sint_offset evm base (4 : Fin 32) (7 : Fin 33)
      ⟨56, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem burnObserveSingleEvalLastTickCumulative {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnObserveSingleAfterLastFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "last") "tickCumulative") =
        .ok (wordToElem (.int int56Int) (burnObserveSingleTickStorageWord σ I)) := by
  rw [evalExpr?]
  have hlast :
      evalExpr? (config v) (burnObserveSingleAfterLastFrame v σ I)
          (initState cA gh bl σ σ₀ g A I) (.var "last") =
        .ok (.storageRef (burnObserveSingleLastEvaledRef σ I) observationStructTy) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [burnObserveSingleAfterLast_last (v := v) (σ := σ) (I := I)]
  rw [hlast]
  simp only [EvalResult.ofOption, EvalResult.bind, bind]
  change readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnObserveSingleLastFieldEvaledRef σ I "tickCumulative")
      (.elem (.int int56Int)) =
    .ok (wordToElem (.int int56Int) (burnObserveSingleTickStorageWord σ I))
  rw [readStorage?]
  simp only [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
    burnObserveSingleLastFieldEvaledRef, burnObserveSingleObservationKey]
  simpa [initState, burnObserveSingleTickStorageWord, burnObserveSingleTickRawWord,
    burnObserveSingleSlotWord, solcSlotWord]
    using burnObservationStorageLocLoad_tickCumulative (initState cA gh bl σ σ₀ g A I)
      (burnObserveSingleObservationBaseSlot σ I)

theorem burnObservationStorageLocLoad_secondsPerLiquidity (evm : EVM.State)
    (base : UInt256) :
    storageLocLoad evm
        (loc base ⟨11, by decide⟩ ⟨20, by decide⟩
          (by decide) (.int uint160Int)) =
      .int (Int.ofNat (UInt256.land
        (UInt256.div
          (Solm.EVM.storageLoad evm evm.executionEnv.codeOwner base)
          (observationsShiftBytes 11))
        slot0Uint160Mask).toNat) := by
  rw [← show UInt256.ofNat (256 ^ (11 : Nat)) = observationsShiftBytes 11 by rfl]
  rw [← show UInt256.ofNat (256 ^ (20 : Nat) - 1) = slot0Uint160Mask by native_decide]
  simpa [loc, uint160Int] using
    storageLocLoad_uint_offset evm base (11 : Fin 32) (20 : Fin 33)
      ⟨160, by decide⟩ (hbound := by decide) (by decide) (by decide)

theorem burnObserveSingleEvalLastSecondsPerLiquidity {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) (burnObserveSingleAfterLastFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.field (.var "last") "secondsPerLiquidityCumulativeX128") =
        .ok (.int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat)) := by
  rw [evalExpr?]
  have hlast :
      evalExpr? (config v) (burnObserveSingleAfterLastFrame v σ I)
          (initState cA gh bl σ σ₀ g A I) (.var "last") =
        .ok (.storageRef (burnObserveSingleLastEvaledRef σ I) observationStructTy) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [burnObserveSingleAfterLast_last (v := v) (σ := σ) (I := I)]
  rw [hlast]
  simp only [EvalResult.ofOption, EvalResult.bind, bind]
  change readStorage? (config v) (initState cA gh bl σ σ₀ g A I)
      (burnObserveSingleLastFieldEvaledRef σ I "secondsPerLiquidityCumulativeX128")
      (.elem (.int uint160Int)) =
    .ok (.int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat))
  rw [readStorage?]
  simp only [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
    burnObserveSingleLastFieldEvaledRef, burnObserveSingleObservationKey]
  simpa [initState, burnObserveSingleSecondsPerLiquidityWord, burnObserveSingleSlotWord,
    solcSlotWord]
    using burnObservationStorageLocLoad_secondsPerLiquidity
      (initState cA gh bl σ σ₀ g A I) (burnObserveSingleObservationBaseSlot σ I)

def burnObserveSingleRawLastFieldEvaledRef (σ : AccountMap) (I : ExecutionEnv)
    (field : Ident) : EvaledStorageRef :=
  { base := "observationsRaw",
    steps := [.mindex (burnObserveSingleObservationKey σ I), .field field] }

theorem burnObserveSingleEvalStorageRef_observationsRaw {v : PoolImmutables}
    (evm : EVM.State) (σ : AccountMap) (I : ExecutionEnv) (field : Ident) :
    evalStorageRef (config v) { contract := contract v, locals := burnObserveSingleStore σ I }
      evm (observationsRawF (.var "index") field) =
        .ok (burnObserveSingleRawLastFieldEvaledRef σ I field) := by
  simp [evalStorageRef, evalStorageRefStep, evalStorageRefSteps, observationsRawF,
    burnObserveSingleRawLastFieldEvaledRef, burnObserveSingleEvalIndex,
    burnSlot0ObservationIndexValue, burnObserveSingleObservationKey, valueToKey?,
    EvalResult.bind, EvalResult.ofOption, bind, pure]

theorem burnObserveSingleEvalRawBlockTimestamp {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (observationsRawF (.var "index") "blockTimestamp")) =
        .ok (.int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat)) := by
  apply evalExpr_storage_scalar_value
      (er := burnObserveSingleRawLastFieldEvaledRef σ I "blockTimestamp")
      (t := .int uint32Int)
      (loc := loc (burnObserveSingleObservationBaseSlot σ I) ⟨0, by decide⟩
        ⟨4, by decide⟩ (by decide) (.int uint32Int))
  · simp [burnObserveSingleStore, observationsRawF]
  · exact burnObserveSingleEvalStorageRef_observationsRaw
      (v := v) (initState cA gh bl σ σ₀ g A I) σ I "blockTimestamp"
  · simp [burnObserveSingleRawLastFieldEvaledRef, contract, storageDecls, storageTypeAt?,
      storageTypeStep?, observationStructTy, uint32St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnObserveSingleRawLastFieldEvaledRef, burnObserveSingleObservationKey,
      burnObserveSingleObservationBaseSlot, loc]
  · simpa [initState, burnObserveSingleBlockTimestampWord, burnObserveSingleSlotWord,
      solcSlotWord] using
      burnObservationStorageLocLoad_blockTimestamp (initState cA gh bl σ σ₀ g A I)
        (burnObserveSingleObservationBaseSlot σ I)

theorem burnObserveSingleEvalRawTimestampNeTimeFalse {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hsame :
      .int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat) =
        burnBlockTimestamp32Value I) :
    evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I }
      (initState cA gh bl σ σ₀ g A I)
      (neE (.storage (observationsRawF (.var "index") "blockTimestamp")) (.var "time")) =
        .ok (.bool false) := by
  unfold neE
  rw [evalExpr?] <;> try decide
  rw [burnObserveSingleEvalRawBlockTimestamp (v := v)
    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
    (I := I) (g := g)]
  have htime :
      evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I }
        (initState cA gh bl σ σ₀ g A I) (.var "time") =
          .ok (burnBlockTimestamp32Value I) := by
    simp only [evalExpr?, EvalResult.ofOption]
    rw [burnObserveSingleStore_time σ I]
  rw [htime]
  rw [hsame]
  simp [EvalResult.bind, bind, evalBinaryOp?, burnBlockTimestamp32Value]

theorem burnObserveSingleEvalRawTickCumulative {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (observationsRawF (.var "index") "tickCumulative")) =
        .ok (wordToElem (.int int56Int) (burnObserveSingleTickStorageWord σ I)) := by
  apply evalExpr_storage_scalar_value
      (er := burnObserveSingleRawLastFieldEvaledRef σ I "tickCumulative")
      (t := .int int56Int)
      (loc := loc (burnObserveSingleObservationBaseSlot σ I) ⟨4, by decide⟩
        ⟨7, by decide⟩ (by decide) (.int int56Int))
  · simp [burnObserveSingleStore, observationsRawF]
  · exact burnObserveSingleEvalStorageRef_observationsRaw
      (v := v) (initState cA gh bl σ σ₀ g A I) σ I "tickCumulative"
  · simp [burnObserveSingleRawLastFieldEvaledRef, contract, storageDecls, storageTypeAt?,
      storageTypeStep?, observationStructTy, int56St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnObserveSingleRawLastFieldEvaledRef, burnObserveSingleObservationKey,
      burnObserveSingleObservationBaseSlot, loc]
  · simpa [initState, burnObserveSingleTickStorageWord, burnObserveSingleTickRawWord,
      burnObserveSingleSlotWord, solcSlotWord] using
      burnObservationStorageLocLoad_tickCumulative (initState cA gh bl σ σ₀ g A I)
        (burnObserveSingleObservationBaseSlot σ I)

theorem burnObserveSingleEvalRawSecondsPerLiquidity {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256} :
    evalExpr? (config v) { contract := contract v, locals := burnObserveSingleStore σ I }
      (initState cA gh bl σ σ₀ g A I)
      (.storage (observationsRawF (.var "index")
        "secondsPerLiquidityCumulativeX128")) =
        .ok (.int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat)) := by
  apply evalExpr_storage_scalar_value
      (er := burnObserveSingleRawLastFieldEvaledRef σ I
        "secondsPerLiquidityCumulativeX128")
      (t := .int uint160Int)
      (loc := loc (burnObserveSingleObservationBaseSlot σ I) ⟨11, by decide⟩
        ⟨20, by decide⟩ (by decide) (.int uint160Int))
  · simp [burnObserveSingleStore, observationsRawF]
  · exact burnObserveSingleEvalStorageRef_observationsRaw
      (v := v) (initState cA gh bl σ σ₀ g A I)
      σ I "secondsPerLiquidityCumulativeX128"
  · simp [burnObserveSingleRawLastFieldEvaledRef, contract, storageDecls, storageTypeAt?,
      storageTypeStep?, observationStructTy, uint160St]
  · funext evm
    simp [config, storageLayout, storageLayoutRaw, solidityStorageLayout,
      burnObserveSingleRawLastFieldEvaledRef, burnObserveSingleObservationKey,
      burnObserveSingleObservationBaseSlot, loc]
  · simpa [initState, burnObserveSingleSecondsPerLiquidityWord, burnObserveSingleSlotWord,
      solcSlotWord] using
      burnObservationStorageLocLoad_secondsPerLiquidity
        (initState cA gh bl σ σ₀ g A I) (burnObserveSingleObservationBaseSlot σ I)

abbrev burnObserveSingleTimestampEqualReturnValues (σ : AccountMap) (I : ExecutionEnv) :
    List Value :=
  [ wordToElem (.int int56Int) (burnObserveSingleTickStorageWord σ I),
    .int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat) ]

theorem burnObserveSingleTimestampEqualReturnValues_transport {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} (hAccounts : accountMapEquiv σ_evm σ_solm) :
    burnObserveSingleTimestampEqualReturnValues σ_evm I =
      burnObserveSingleTimestampEqualReturnValues σ_solm I := by
  unfold burnObserveSingleTimestampEqualReturnValues
  rw [burnObserveSingleTickStorageWord_transport hAccounts,
    burnObserveSingleSecondsPerLiquidityWord_transport hAccounts]

theorem uniswapV3PoolObserveSingleSourceTimestampEqualReturns {v : PoolImmutables}
    {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbound : (slot0ObservationIndexWord σ I).toNat < 65535)
    (hsame :
      .int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat) =
        burnBlockTimestamp32Value I) :
    ExecFuncBody (config v)
      { contract := contract v, locals := burnObserveSingleStore σ I }
      (initState cA gh bl σ σ₀ g A I) observeSingleFunction.body
      (.returned { contract := contract v, locals := burnObserveSingleStore σ I }
        (initState cA gh bl σ σ₀ g A I)
        (some (burnObserveSingleTimestampEqualReturnValues σ I))) := by
  refine ExecFuncBody.execBlockRet ?_
  simpa [observeSingleFunction] using
    (ExecBlock.consReturn
      (ExecStmt.iteTrue
        (burnObserveSingleEvalSecondsAgoZero (v := v) (σ := σ) (I := I)
          (evm := initState cA gh bl σ σ₀ g A I))
        (ExecBlock.consNormal
          (ExecStmt.requireTrue
            (burnObserveSingleEvalIndexLtBoundTrue (v := v) (cA := cA) (gh := gh)
              (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g) hbound))
          (ExecBlock.consReturn
            (ExecStmt.iteFalse
              (burnObserveSingleEvalRawTimestampNeTimeFalse (v := v)
                (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
                (I := I) (g := g) hsame)
              (ExecBlock.consReturn <| ExecStmt.return (by
                have htick :
                    evalExpr? (config v)
                      { contract := contract v, locals := burnObserveSingleStore σ I }
                      (initState cA gh bl σ σ₀ g A I)
                      (.storage (observationsRawF (.var "index") "tickCumulative")) =
                        .ok (wordToElem (.int int56Int)
                          (burnObserveSingleTickStorageWord σ I)) :=
                  burnObserveSingleEvalRawTickCumulative (v := v)
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                have hseconds :
                    evalExpr? (config v)
                      { contract := contract v, locals := burnObserveSingleStore σ I }
                      (initState cA gh bl σ σ₀ g A I)
                      (.storage (observationsRawF (.var "index")
                        "secondsPerLiquidityCumulativeX128")) =
                        .ok (.int
                          (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat)) :=
                  burnObserveSingleEvalRawSecondsPerLiquidity (v := v)
                    (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀)
                    (A := A) (I := I) (g := g)
                change evalExprs? (config v)
                    { contract := contract v, locals := burnObserveSingleStore σ I }
                    (initState cA gh bl σ σ₀ g A I)
                    [ .storage (observationsRawF (.var "index") "tickCumulative"),
                      .storage (observationsRawF (.var "index")
                        "secondsPerLiquidityCumulativeX128") ] =
                  .ok [ wordToElem (.int int56Int) (burnObserveSingleTickStorageWord σ I),
                    .int (Int.ofNat (burnObserveSingleSecondsPerLiquidityWord σ I).toNat) ]
                rw [evalExprs?]
                rw [htick]
                simp only [EvalResult.bind, bind, pure]
                rw [evalExprs?]
                rw [hseconds]
                rfl)))))))

abbrev burnModifyPositionAfterObserveSingleFrame (v : PoolImmutables) (σ : AccountMap)
    (I : ExecutionEnv) : Frame :=
  { contract := contract v,
    locals := (burnModifyPositionAfterTimeFrame v σ I).locals.insert "observedForUpdate"
      (.tuple (burnObserveSingleTimestampEqualReturnValues σ I)) }

theorem uniswapV3PoolModifyPositionSourceObserveSingleTimestampEqualStep
    {v : PoolImmutables} {cA gh bl σ σ₀ A I} {g : Sat256}
    (hbound : (slot0ObservationIndexWord σ I).toNat < 65535)
    (hsame :
      .int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat) =
        burnBlockTimestamp32Value I) :
    ExecStmt (config v) (burnModifyPositionAfterTimeFrame v σ I)
      (initState cA gh bl σ σ₀ g A I)
      (.internalCall "observeSingle"
        [ .var "time", .intLit 0, .storage (slot0F "tick"),
          .storage (slot0F "observationIndex"), .storage liquidityRef,
          .storage (slot0F "observationCardinality") ]
        "observedForUpdate")
      (.ok (burnModifyPositionAfterObserveSingleFrame v σ I)
        (initState cA gh bl σ σ₀ g A I)) := by
  have hstmt := internalCallFunctionReturn (callee := observeSingleFunction)
    (retVar := "observedForUpdate")
    (argVals := burnObserveSingleArgValues σ I)
    (locals := burnObserveSingleStore σ I)
    (calleeSolm := { contract := contract v, locals := burnObserveSingleStore σ I })
    (value := some (burnObserveSingleTimestampEqualReturnValues σ I))
    (burnModifyPosition_evalObserveSingleArgs (v := v) (cA := cA)
      (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A) (I := I) (g := g))
    (by
      simpa [burnModifyPositionAfterTimeFrame] using uniswapV3PoolLookupObserveSingle v)
    (burnObserveSingle_bindParams σ I)
    (uniswapV3PoolObserveSingleSourceTimestampEqualReturns (v := v)
      (cA := cA) (gh := gh) (bl := bl) (σ := σ) (σ₀ := σ₀) (A := A)
      (I := I) (g := g) hbound hsame)
  simpa [burnModifyPositionAfterObserveSingleFrame, resumeAfterInternalCall,
    collapseReturns] using hstmt

abbrev burnObserveSingleDecodedBlockWord (obsWord : UInt256) : UInt256 :=
  UInt256.land obsWord observationsUint32Mask

private theorem uInt256_eq_word_eq_of_ne_zero {a b : UInt256}
    (h : UInt256.eq a b ≠ ⟨0⟩) :
    a = b := by
  apply uInt256_eq_one_eq
  by_contra hone
  exact h (uInt256_eq_zero_of_ne hone)

theorem burnObserveSingleBlockTimestampValue_eq_of_maskedTimestamp
    (σ : AccountMap) (I : ExecutionEnv)
    (hword : burnObserveSingleBlockTimestampWord σ I =
      UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask) :
    .int (Int.ofNat (burnObserveSingleBlockTimestampWord σ I).toNat) =
      burnBlockTimestamp32Value I := by
  unfold burnBlockTimestamp32Value
  rw [hword, u256_land_toNat, observationsUint32Mask_toNat, nat_land_mask_eq_mod]
  rw [Nat.mod_eq_of_lt (by
    exact lt_trans (Nat.mod_lt _ (by norm_num)) (by norm_num [UInt256.size]))]

theorem burnObserveSingleSourceTimestampEqOfGuard {σ_evm σ_solm : AccountMap}
    {I : ExecutionEnv} {obsWord : UInt256}
    (hAccounts : accountMapEquiv σ_evm σ_solm)
    (hobsWord : obsWord = burnObserveSingleSlotWord σ_evm I)
    (heq : UInt256.eq
      (UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask)
      (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩) :
    .int (Int.ofNat (burnObserveSingleBlockTimestampWord σ_solm I).toNat) =
      burnBlockTimestamp32Value I := by
  have hdecoded :
      burnObserveSingleDecodedBlockWord obsWord =
        burnObserveSingleBlockTimestampWord σ_evm I := by
    rw [hobsWord]
  have hmasked :
      UInt256.land (UInt256.ofNat I.header.timestamp) observationsUint32Mask =
        burnObserveSingleBlockTimestampWord σ_evm I :=
    (uInt256_eq_word_eq_of_ne_zero heq).trans hdecoded
  apply burnObserveSingleBlockTimestampValue_eq_of_maskedTimestamp
  rw [← burnObserveSingleBlockTimestampWord_transport hAccounts]
  exact hmasked.symm

abbrev burnObserveSingleDecodedTickRawWord (obsWord : UInt256) : UInt256 :=
  UInt256.div obsWord (observationsShiftBytes 4)

abbrev burnObserveSingleDecodedTickWord (obsWord : UInt256) : UInt256 :=
  UInt256.signextend ⟨6⟩ (burnObserveSingleDecodedTickRawWord obsWord)

abbrev burnObserveSingleDecodedSecondsWord (obsWord : UInt256) : UInt256 :=
  UInt256.land slot0Uint160Mask (UInt256.div obsWord (observationsShiftBytes 11))

abbrev burnObserveSingleDecodedInitializedWord (obsWord : UInt256) : UInt256 :=
  slot0BoolReturnWord
    (UInt256.land slot0Uint8Mask (UInt256.div obsWord (observationsShiftBytes 31)))

noncomputable abbrev burnObserveSingleDecodedMem1 (σ : AccountMap) (I : ExecutionEnv)
    (obsWord : UInt256) : ByteArray :=
  writeWord (burnObserveSingleAllocMem σ I) burnPositionKeyNewFreePtrWord.toNat
    (burnObserveSingleDecodedBlockWord obsWord)

noncomputable abbrev burnObserveSingleDecodedMem2 (σ : AccountMap) (I : ExecutionEnv)
    (obsWord : UInt256) : ByteArray :=
  writeWord (burnObserveSingleDecodedMem1 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (burnObserveSingleDecodedTickWord obsWord)

noncomputable abbrev burnObserveSingleDecodedMem3 (σ : AccountMap) (I : ExecutionEnv)
    (obsWord : UInt256) : ByteArray :=
  writeWord (burnObserveSingleDecodedMem2 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (burnObserveSingleDecodedSecondsWord obsWord)

noncomputable abbrev burnObserveSingleDecodedMem (σ : AccountMap) (I : ExecutionEnv)
    (obsWord : UInt256) : ByteArray :=
  writeWord (burnObserveSingleDecodedMem3 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    (burnObserveSingleDecodedInitializedWord obsWord)

theorem burnObserveSingleAllocMem_size (σ : AccountMap) (I : ExecutionEnv) :
    (burnObserveSingleAllocMem σ I).size = 567 := by
  unfold burnObserveSingleAllocMem
  rw [writeWord_size _ _ _ (by rw [burnPositionKeyMappingMem_size σ I]; native_decide)]
  rw [burnPositionKeyMappingMem_size σ I]
  native_decide

theorem burnObserveSingleDecodedMem1_size (σ : AccountMap) (I : ExecutionEnv)
    (obsWord : UInt256) :
    (burnObserveSingleDecodedMem1 σ I obsWord).size = 570 := by
  unfold burnObserveSingleDecodedMem1
  rw [writeWord_size _ _ _ (by rw [burnObserveSingleAllocMem_size σ I]; native_decide)]
  rw [burnObserveSingleAllocMem_size σ I]
  native_decide

theorem burnObserveSingleDecodedMem2_size (σ : AccountMap) (I : ExecutionEnv)
    (obsWord : UInt256) :
    (burnObserveSingleDecodedMem2 σ I obsWord).size = 602 := by
  unfold burnObserveSingleDecodedMem2
  rw [writeWord_size _ _ _ (by
    rw [burnObserveSingleDecodedMem1_size σ I obsWord]
    native_decide)]
  rw [burnObserveSingleDecodedMem1_size σ I obsWord]
  native_decide

theorem burnObserveSingleDecodedMem3_size (σ : AccountMap) (I : ExecutionEnv)
    (obsWord : UInt256) :
    (burnObserveSingleDecodedMem3 σ I obsWord).size = 634 := by
  unfold burnObserveSingleDecodedMem3
  rw [writeWord_size _ _ _ (by
    rw [burnObserveSingleDecodedMem2_size σ I obsWord]
    native_decide)]
  rw [burnObserveSingleDecodedMem2_size σ I obsWord]
  native_decide

theorem burnObserveSingleDecodedMem_size (σ : AccountMap) (I : ExecutionEnv)
    (obsWord : UInt256) :
    (burnObserveSingleDecodedMem σ I obsWord).size = 666 := by
  unfold burnObserveSingleDecodedMem
  rw [writeWord_size _ _ _ (by
    rw [burnObserveSingleDecodedMem3_size σ I obsWord]
    native_decide)]
  rw [burnObserveSingleDecodedMem3_size σ I obsWord]
  native_decide

theorem burnObserveSingleDecodedMem_readFreePtrPlus32 (σ : AccountMap)
    (I : ExecutionEnv) (obsWord : UInt256) :
    (burnObserveSingleDecodedMem σ I obsWord).readWithPadding
        (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat 32 =
      UInt256.toByteArray (burnObserveSingleDecodedTickWord obsWord) := by
  unfold burnObserveSingleDecodedMem
  rw [writeWord_read_preserved
    (burnObserveSingleDecodedMem3 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (burnObserveSingleDecodedInitializedWord obsWord)
    (by rw [burnObserveSingleDecodedMem3_size σ I obsWord]; native_decide)
    (by rw [burnObserveSingleDecodedMem3_size σ I obsWord]; native_decide)]
  unfold burnObserveSingleDecodedMem3
  rw [writeWord_read_preserved
    (burnObserveSingleDecodedMem2 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (burnObserveSingleDecodedSecondsWord obsWord)
    (by rw [burnObserveSingleDecodedMem2_size σ I obsWord]; native_decide)
    (by rw [burnObserveSingleDecodedMem2_size σ I obsWord]; native_decide)]
  unfold burnObserveSingleDecodedMem2
  exact writeWord_read_back (burnObserveSingleDecodedMem1 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat
    (burnObserveSingleDecodedTickWord obsWord)
    (by rw [burnObserveSingleDecodedMem1_size σ I obsWord]; native_decide)

theorem burnObserveSingleDecodedMem_mloadFreePtrPlus32 (σ : AccountMap)
    (I : ExecutionEnv) (obsWord : UInt256) :
    (if (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat ≥
          (burnObserveSingleDecodedMem σ I obsWord).size
        ∨ (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)) ≥
          UInt256.ofNat 21 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnObserveSingleDecodedMem σ I obsWord).readWithPadding
            (burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256)).toNat 32))) =
      burnObserveSingleDecodedTickWord obsWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnObserveSingleDecodedMem σ I obsWord) (aw := UInt256.ofNat 21)
    (off := burnPositionKeyNewFreePtrWord + (⟨32⟩ : UInt256))
    (v := burnObserveSingleDecodedTickWord obsWord)
    (by rw [burnObserveSingleDecodedMem_size σ I obsWord]; native_decide)
    (by native_decide)
    (burnObserveSingleDecodedMem_readFreePtrPlus32 σ I obsWord)

theorem burnObserveSingleDecodedMem_readFreePtrPlus64 (σ : AccountMap)
    (I : ExecutionEnv) (obsWord : UInt256) :
    (burnObserveSingleDecodedMem σ I obsWord).readWithPadding
        (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat 32 =
      UInt256.toByteArray (burnObserveSingleDecodedSecondsWord obsWord) := by
  unfold burnObserveSingleDecodedMem
  rw [writeWord_read_preserved
    (burnObserveSingleDecodedMem3 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨96⟩ : UInt256)).toNat
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (burnObserveSingleDecodedInitializedWord obsWord)
    (by rw [burnObserveSingleDecodedMem3_size σ I obsWord]; native_decide)
    (by rw [burnObserveSingleDecodedMem3_size σ I obsWord]; native_decide)]
  unfold burnObserveSingleDecodedMem3
  exact writeWord_read_back (burnObserveSingleDecodedMem2 σ I obsWord)
    (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat
    (burnObserveSingleDecodedSecondsWord obsWord)
    (by rw [burnObserveSingleDecodedMem2_size σ I obsWord]; native_decide)

theorem burnObserveSingleDecodedMem_mloadFreePtrPlus64 (σ : AccountMap)
    (I : ExecutionEnv) (obsWord : UInt256) :
    (if (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat ≥
          (burnObserveSingleDecodedMem σ I obsWord).size
        ∨ (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)) ≥
          UInt256.ofNat 21 * ⟨32⟩ then ⟨0⟩
      else UInt256.ofNat
        (fromByteArrayBigEndian
          ((burnObserveSingleDecodedMem σ I obsWord).readWithPadding
            (burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256)).toNat 32))) =
      burnObserveSingleDecodedSecondsWord obsWord := by
  exact mloadWordValue_of_readWithPadding
    (mem := burnObserveSingleDecodedMem σ I obsWord) (aw := UInt256.ofNat 21)
    (off := burnPositionKeyNewFreePtrWord + (⟨64⟩ : UInt256))
    (v := burnObserveSingleDecodedSecondsWord obsWord)
    (by rw [burnObserveSingleDecodedMem_size σ I obsWord]; native_decide)
    (by native_decide)
    (burnObserveSingleDecodedMem_readFreePtrPlus64 σ I obsWord)

private theorem uniswapV3PoolBurnObserveSingleReturnDecodeEqTemplate
    {v : PoolImmutables} {code : ByteArray} {pc : UInt256}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (hlo : 13242 ≤ pc.toNat) (hhi : pc.toNat + 33 ≤ 13628) :
    decode code pc = decode uniswapV3PoolBytecode pc := by
  exact uniswapV3PoolDecodePatchedEqTemplateDisjoint hpatch
    (by
      have hsize : 13628 ≤ uniswapV3PoolBytecode.size := by native_decide
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

private theorem uniswapV3PoolBurnObserveSinglePatchPreservesJumpDest13340 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13340⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched13340 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13340⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnObserveSinglePatchPreservesJumpDest13340

private theorem uniswapV3PoolBurnObserveSinglePatchPreservesJumpDest13584 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨13584⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched13584 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨13584⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnObserveSinglePatchPreservesJumpDest13584

private theorem uniswapV3PoolBurnObserveSinglePatchPreservesJumpDest19273 :
    D_J_auxPreservesTargetBool uniswapV3PoolBytecode uniswapV3PoolPatchOffsets
      ⟨19273⟩ 0 = true := by
  native_decide

theorem uniswapV3PoolBurnJumpDestPatched19273 {v : PoolImmutables} {code : ByteArray}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code) :
    (D_J code 0).contains ⟨19273⟩ = true := by
  exact D_J_aux_contains_of_patchRuntime_preservesTarget hpatch
    (uniswapV3PoolPatchOffsetMem v)
    uniswapV3PoolBurnObserveSinglePatchPreservesJumpDest19273

theorem uniswapV3PoolBurnObserveSingleTimestampEqualJump
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {obsWord cardinality liquidity index tick time ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13242⟩
      (obsWord :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time :: ⟨8⟩ :: ret :: R)
      (burnObserveSingleAllocMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (heq : UInt256.eq (UInt256.land time observationsUint32Mask)
        (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ⟨13340⟩
      (burnPositionKeyNewFreePtrWord :: ⟨0⟩ :: ⟨0⟩ :: cardinality :: liquidity ::
        index :: tick :: ⟨0⟩ :: time :: ⟨8⟩ :: ret :: R)
      (burnObserveSingleDecodedMem σ ee obsWord) (UInt256.ofNat 21) rdata (cA, σ) k' C' := by
  have hdecode {pc : UInt256} (hlo : 13242 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 13628) :
      decode code pc = decode uniswapV3PoolBytecode pc :=
    uniswapV3PoolBurnObserveSingleReturnDecodeEqTemplate hpatch hlo hhi
  have hd13242 : decode code ⟨13242⟩ =
      some (.Push .PUSH4, some (⟨4294967295⟩, 4)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13247 : decode code ⟨13247⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13248 : decode code ⟨13248⟩ = some (.DUP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13249 : decode code ⟨13249⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13250 : decode code ⟨13250⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13251 : decode code ⟨13251⟩ = some (.DUP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13252 : decode code ⟨13252⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13253 : decode code ⟨13253⟩ =
      some (.Push .PUSH5, some (⟨4294967296⟩, 5)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13259 : decode code ⟨13259⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13260 : decode code ⟨13260⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13261 : decode code ⟨13261⟩ = some (.Push .PUSH1, some (⟨6⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13263 : decode code ⟨13263⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13264 : decode code ⟨13264⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13265 : decode code ⟨13265⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13266 : decode code ⟨13266⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13267 : decode code ⟨13267⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13268 : decode code ⟨13268⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13269 : decode code ⟨13269⟩ = some (.SIGNEXTEND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13270 : decode code ⟨13270⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13272 : decode code ⟨13272⟩ = some (.DUP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13273 : decode code ⟨13273⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13274 : decode code ⟨13274⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13275 : decode code ⟨13275⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13277 : decode code ⟨13277⟩ = some (.Push .PUSH1, some (⟨88⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13279 : decode code ⟨13279⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13280 : decode code ⟨13280⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13281 : decode code ⟨13281⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13282 : decode code ⟨13282⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13284 : decode code ⟨13284⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13286 : decode code ⟨13286⟩ = some (.Push .PUSH1, some (⟨160⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13288 : decode code ⟨13288⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13289 : decode code ⟨13289⟩ = some (.SUB, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13290 : decode code ⟨13290⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13291 : decode code ⟨13291⟩ = some (.SWAP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13292 : decode code ⟨13292⟩ = some (.DUP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13293 : decode code ⟨13293⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13294 : decode code ⟨13294⟩ = some (.SWAP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13295 : decode code ⟨13295⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13296 : decode code ⟨13296⟩ = some (.SWAP5, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13297 : decode code ⟨13297⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13298 : decode code ⟨13298⟩ = some (.Push .PUSH1, some (⟨1⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13300 : decode code ⟨13300⟩ = some (.Push .PUSH1, some (⟨248⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13302 : decode code ⟨13302⟩ = some (.SHL, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13303 : decode code ⟨13303⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13304 : decode code ⟨13304⟩ = some (.SWAP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13305 : decode code ⟨13305⟩ = some (.DIV, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13306 : decode code ⟨13306⟩ = some (.Push .PUSH1, some (⟨255⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13308 : decode code ⟨13308⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13309 : decode code ⟨13309⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13310 : decode code ⟨13310⟩ = some (.ISZERO, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13311 : decode code ⟨13311⟩ = some (.Push .PUSH1, some (⟨96⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13313 : decode code ⟨13313⟩ = some (.DUP4, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13314 : decode code ⟨13314⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13315 : decode code ⟨13315⟩ = some (.MSTORE, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13316 : decode code ⟨13316⟩ = some (.SWAP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13317 : decode code ⟨13317⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13318 : decode code ⟨13318⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13319 : decode code ⟨13319⟩ = some (.DUP11, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13320 : decode code ⟨13320⟩ = some (.AND, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13321 : decode code ⟨13321⟩ = some (.EQ, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13322 : decode code ⟨13322⟩ = some (.Push .PUSH2, some (⟨13340⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13325 : decode code ⟨13325⟩ = some (.JUMPI, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have h13252 := evm_run h with [
    raw push4 ⟨4294967295⟩ hd13242 (by evm_ov),
    raw dup1 hd13247 (by evm_ov),
    raw dup3 hd13248 (by evm_ov),
    raw and hd13249 (by evm_ov),
    raw dup1 hd13250 (by evm_ov),
    raw dup5 hd13251 (by evm_ov)]
  have h13253 := h13252.mstore 0 (burnObserveSingleDecodedMem1 σ ee obsWord)
    (UInt256.ofNat 18) hd13252 mem_cost
    (by
      dsimp [burnObserveSingleDecodedMem1, burnObserveSingleDecodedBlockWord]
      rw [show (⟨4294967295⟩ : UInt256) = observationsUint32Mask by native_decide]
      rfl)
    (by native_decide)
    (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h13259 := by
    simpa [burnObserveSingleDecodedBlockWord] using
      h13253.pushConst ⟨4294967296⟩
        (by decide : Operation.POp.PUSH5 ≠ .PUSH0) hd13253 (by
          have hlen := hov
          simp only [List.length_cons] at hlen ⊢
          omega)
  have h13265pre := evm_run h13259 with [
    raw dup4 hd13259 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw div hd13260 (by evm_ov),
    raw push1 ⟨6⟩ hd13261 (by evm_ov),
    raw swap1 hd13263 (by evm_ov),
    raw dup2 hd13264 (by evm_ov)]
  have h13266 := RD.signextend h13265pre hd13265 (by evm_ov)
  have h13267pre := evm_run h13266 with [
    raw dup2 hd13266 (by evm_ov)]
  have h13268 := RD.signextend h13267pre hd13267 (by evm_ov)
  have h13269pre := evm_run h13268 with [
    raw swap1 hd13268 (by evm_ov)]
  have h13270 := RD.signextend h13269pre hd13269 (by evm_ov)
  have h13274pre := evm_run h13270 with [
    raw push1 ⟨32⟩ hd13270 (by evm_ov),
    raw dup6 hd13272 (by evm_ov),
    raw add hd13273 (by evm_ov)]
  have h13275 := h13274pre.mstore 3 (burnObserveSingleDecodedMem2 σ ee obsWord)
    (UInt256.ofNat 19) hd13274 mem_cost
    (by
      rw [show (⟨4294967296⟩ : UInt256) = observationsShiftBytes 4 by native_decide]
      simp [burnObserveSingleDecodedMem2, burnObserveSingleDecodedMem1,
        burnObserveSingleDecodedTickWord, burnObserveSingleDecodedTickRawWord,
        burnObserveSingleDecodedBlockWord, observationsSignextendSix_idempotent,
        Reasoning.Theory.writeWord, u256_add_comm])
    (by native_decide)
    (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h13297pre := evm_run h13275 with [
    raw push1 ⟨1⟩ hd13275 (by evm_ov),
    raw push1 ⟨88⟩ hd13277 (by evm_ov),
    raw shl hd13279 (by evm_ov),
    raw dup4 hd13280 (by evm_ov),
    raw div hd13281 (by evm_ov),
    raw push1 ⟨1⟩ hd13282 (by evm_ov),
    raw push1 ⟨1⟩ hd13284 (by evm_ov),
    raw push1 ⟨160⟩ hd13286 (by evm_ov),
    raw shl hd13288 (by evm_ov),
    raw sub hd13289 (by evm_ov),
    raw and hd13290 (by evm_ov),
    raw swap5 hd13291 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw dup5 hd13292 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw add hd13293 (by evm_ov),
    raw swap5 hd13294 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw swap1 hd13295 (by evm_ov),
    raw swap5 hd13296 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)]
  have h13298 := h13297pre.mstore 3 (burnObserveSingleDecodedMem3 σ ee obsWord)
    (UInt256.ofNat 20) hd13297 mem_cost
    (by
      rw [
        show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨88⟩ = observationsShiftBytes 11 by
          native_decide,
        show UInt256.sub (UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨160⟩) ⟨1⟩ =
            slot0Uint160Mask by
          native_decide]
      simp [burnObserveSingleDecodedMem3, burnObserveSingleDecodedMem2,
        burnObserveSingleDecodedMem1, burnObserveSingleDecodedSecondsWord,
        burnObserveSingleDecodedTickWord, burnObserveSingleDecodedTickRawWord,
        burnObserveSingleDecodedBlockWord, Reasoning.Theory.writeWord, u256_add_comm])
    (by native_decide)
    (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h13315pre := evm_run h13298 with [
    raw push1 ⟨1⟩ hd13298 (by evm_ov),
    raw push1 ⟨248⟩ hd13300 (by evm_ov),
    raw shl hd13302 (by evm_ov),
    raw swap1 hd13303 (by evm_ov),
    raw swap2 hd13304 (by evm_ov),
    raw div hd13305 (by evm_ov),
    raw push1 ⟨255⟩ hd13306 (by evm_ov),
    raw and hd13308 (by evm_ov),
    raw iszero hd13309 (by evm_ov),
    raw iszero hd13310 (by evm_ov),
    raw push1 ⟨96⟩ hd13311 (by evm_ov),
    raw dup4 hd13313 (by evm_ov),
    raw add hd13314 (by evm_ov)]
  have h13316 := h13315pre.mstore 3 (burnObserveSingleDecodedMem σ ee obsWord)
    (UInt256.ofNat 21) hd13315 mem_cost
    (by
      rw [show (⟨255⟩ : UInt256) = slot0Uint8Mask by native_decide,
        show UInt256.shiftLeft (⟨1⟩ : UInt256) ⟨248⟩ = observationsShiftBytes 31 by
          native_decide]
      simp [burnObserveSingleDecodedMem, burnObserveSingleDecodedMem3,
        burnObserveSingleDecodedMem2, burnObserveSingleDecodedMem1,
        burnObserveSingleDecodedInitializedWord, burnObserveSingleDecodedSecondsWord,
        burnObserveSingleDecodedTickWord, burnObserveSingleDecodedTickRawWord,
        burnObserveSingleDecodedBlockWord, slot0BoolReturnWord, Reasoning.Theory.writeWord,
        u256_add_comm])
    (by native_decide)
    (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h13322pre := evm_run h13316 with [
    raw swap1 hd13316 (by evm_ov),
    raw swap3 hd13317 (by evm_ov),
    raw pop hd13318 (by evm_ov),
    raw dup11 hd13319 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw and hd13320 (by evm_ov),
    raw eq hd13321 (by evm_ov)]
  have h13325 := evm_run h13322pre with [
    raw push2 ⟨13340⟩ hd13322 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)]
  rw [show (⟨4294967295⟩ : UInt256) = observationsUint32Mask by native_decide] at h13325
  exact ⟨_, _, h13325.jumpiT hd13325 heq
    (uniswapV3PoolBurnJumpDestPatched13340 hpatch) (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)⟩

theorem uniswapV3PoolBurnObserveSingleTimestampEqualReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {obsWord cardinality liquidity index tick time memPtr ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13340⟩
      (burnPositionKeyNewFreePtrWord :: ⟨0⟩ :: ⟨0⟩ :: cardinality :: liquidity ::
        index :: tick :: ⟨0⟩ :: time :: memPtr :: ret :: R)
      (burnObserveSingleDecodedMem σ ee obsWord) (UInt256.ofNat 21) rdata (cA, σ) k C)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 14 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (burnObserveSingleDecodedSecondsWord obsWord ::
        burnObserveSingleDecodedTickWord obsWord :: R)
      (burnObserveSingleDecodedMem σ ee obsWord) (UInt256.ofNat 21) rdata (cA, σ) k' C' := by
  have hdecode {pc : UInt256} (hlo : 13242 ≤ pc.toNat)
      (hhi : pc.toNat + 33 ≤ 13628) :
      decode code pc = decode uniswapV3PoolBytecode pc :=
    uniswapV3PoolBurnObserveSingleReturnDecodeEqTemplate hpatch hlo hhi
  have hd13340 : decode code ⟨13340⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13341 : decode code ⟨13341⟩ = some (.DUP1, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13342 : decode code ⟨13342⟩ = some (.Push .PUSH1, some (⟨32⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13344 : decode code ⟨13344⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13345 : decode code ⟨13345⟩ = some (.MLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13346 : decode code ⟨13346⟩ = some (.DUP2, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13347 : decode code ⟨13347⟩ = some (.Push .PUSH1, some (⟨64⟩, 1)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13349 : decode code ⟨13349⟩ = some (.ADD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13350 : decode code ⟨13350⟩ = some (.MLOAD, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13351 : decode code ⟨13351⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13352 : decode code ⟨13352⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13353 : decode code ⟨13353⟩ = some (.SWAP3, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13354 : decode code ⟨13354⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13355 : decode code ⟨13355⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13356 : decode code ⟨13356⟩ =
      some (.Push .PUSH2, some (⟨13584⟩, 2)) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13359 : decode code ⟨13359⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13584 : decode code ⟨13584⟩ = some (.JUMPDEST, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13585 : decode code ⟨13585⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13586 : decode code ⟨13586⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13587 : decode code ⟨13587⟩ = some (.SWAP8, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13588 : decode code ⟨13588⟩ = some (.SWAP6, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13589 : decode code ⟨13589⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13590 : decode code ⟨13590⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13591 : decode code ⟨13591⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13592 : decode code ⟨13592⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13593 : decode code ⟨13593⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13594 : decode code ⟨13594⟩ = some (.POP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have hd13595 : decode code ⟨13595⟩ = some (.JUMP, .none) := by
    rw [hdecode (by native_decide) (by native_decide)]
    native_decide
  have h13345 := evm_run h with [
    raw jumpdest hd13340 (by evm_ov),
    raw dup1 hd13341 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw push1 ⟨32⟩ hd13342 (by evm_ov),
    raw add hd13344 (by evm_ov)]
  have h13346 := by
    simpa using
      h13345.mload 0 (burnObserveSingleDecodedTickWord obsWord)
        (UInt256.ofNat 21) hd13345 mem_cost
        (burnObserveSingleDecodedMem_mloadFreePtrPlus32 σ ee obsWord)
        (by native_decide)
        (by
          have hlen := hov
          simp only [List.length_cons] at hlen ⊢
          omega)
  have h13350 := evm_run h13346 with [
    raw dup2 hd13346 (by evm_ov),
    raw push1 ⟨64⟩ hd13347 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw add hd13349 (by evm_ov)]
  have h13351 := by
    simpa using
      h13350.mload 0 (burnObserveSingleDecodedSecondsWord obsWord)
        (UInt256.ofNat 21) hd13350 mem_cost
        (burnObserveSingleDecodedMem_mloadFreePtrPlus64 σ ee obsWord)
        (by native_decide)
        (by
          have hlen := hov
          simp only [List.length_cons] at hlen ⊢
          omega)
  have h13359 := evm_run h13351 with [
    raw swap3 hd13351 (by evm_ov),
    raw pop hd13352 (by evm_ov),
    raw swap3 hd13353 (by evm_ov),
    raw pop hd13354 (by evm_ov),
    raw pop hd13355 (by evm_ov),
    raw push2 ⟨13584⟩ hd13356 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)]
  have h13584 := h13359.jump hd13359
    (uniswapV3PoolBurnJumpDestPatched13584 hpatch) (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega)
  have h13595 := evm_run h13584 with [
    raw jumpdest hd13584 (by evm_ov),
    raw swap8 hd13585 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw pop hd13586 (by evm_ov),
    raw swap8 hd13587 (by
      have hlen := hov
      omega),
    raw swap6 hd13588 (by
      have hlen := hov
      simp only [List.length_cons] at hlen ⊢
      omega),
    raw pop hd13589 (by evm_ov),
    raw pop hd13590 (by evm_ov),
    raw pop hd13591 (by evm_ov),
    raw pop hd13592 (by evm_ov),
    raw pop hd13593 (by evm_ov),
    raw pop hd13594 (by evm_ov)]
  exact ⟨_, _, h13595.jump hd13595 hret (by
    have hlen := hov
    simp only [List.length_cons] at hlen ⊢
    omega)⟩

theorem uniswapV3PoolBurnObserveSingleTimestampEqualLoadedReturn
    {v : PoolImmutables} {code : ByteArray} {ee : ExecutionEnv} {g : Sat256}
    {s0 : State} {obsWord cardinality liquidity index tick time ret : UInt256}
    {R : List UInt256} {rdata : ByteArray}
    {cA : Batteries.RBSet AccountAddress compare} {σ : AccountMap} {k C : ℕ}
    (hpatch : patchRuntime uniswapV3PoolBytecode (patches v) = some code)
    (h : RD code ee g s0 ⟨13242⟩
      (obsWord :: burnPositionKeyNewFreePtrWord :: ⟨64⟩ :: ⟨0⟩ :: ⟨0⟩ :: ⟨0⟩ ::
        cardinality :: liquidity :: index :: tick :: ⟨0⟩ :: time :: ⟨8⟩ :: ret :: R)
      (burnObserveSingleAllocMem σ ee) (UInt256.ofNat 18) rdata (cA, σ) k C)
    (heq : UInt256.eq (UInt256.land time observationsUint32Mask)
        (burnObserveSingleDecodedBlockWord obsWord) ≠ ⟨0⟩)
    (hret : (D_J code 0).contains ret = true)
    (hov : R.length + 25 ≤ 1024) :
    ∃ k' C', RD code ee g s0 ret
      (burnObserveSingleDecodedSecondsWord obsWord ::
        burnObserveSingleDecodedTickWord obsWord :: R)
      (burnObserveSingleDecodedMem σ ee obsWord) (UInt256.ofNat 21) rdata (cA, σ) k' C' := by
  obtain ⟨_, _, hjump⟩ :=
    uniswapV3PoolBurnObserveSingleTimestampEqualJump
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (obsWord := obsWord) (cardinality := cardinality) (liquidity := liquidity)
      (index := index) (tick := tick) (time := time) (ret := ret) (R := R)
      (rdata := rdata) (cA := cA) (σ := σ) hpatch h heq hov
  exact
    uniswapV3PoolBurnObserveSingleTimestampEqualReturn
      (v := v) (code := code) (ee := ee) (g := g) (s0 := s0)
      (obsWord := obsWord) (cardinality := cardinality) (liquidity := liquidity)
      (index := index) (tick := tick) (time := time) (memPtr := ⟨8⟩) (ret := ret)
      (R := R) (rdata := rdata) (cA := cA) (σ := σ) hpatch hjump hret (by omega)

end Benchmarks.UniswapV3Pool
